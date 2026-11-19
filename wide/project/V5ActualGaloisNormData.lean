import V5ActualGaloisGermFamily
import V5BroadNormBlockEndpoint

noncomputable section
set_option maxHeartbeats 1900000
open scoped BigOperators Topology
namespace StrictEUnit
local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

def v5GaloisFactor (K : IntermediateField ℚ AlgebraicComplex) (a : ℕ → K)
    (σ : K ≃ₐ[ℚ] K) : ℂ → ℂ :=
  exponentialGeneratingFunction (fun n => ((σ (a n) : AlgebraicComplex) : ℂ))

theorem v5_galois_factor_arithmetic (K : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → K) (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (σ : K ≃ₐ[ℚ] K) : V5BroadAlgebraicArithmetic (fun n => (σ (a n) : AlgebraicComplex)) := by
  let τ := σ.liftNormal AlgebraicComplex
  have e (n : ℕ) : τ (a n : AlgebraicComplex) = (σ (a n) : AlgebraicComplex) :=
    σ.liftNormal_commutes AlgebraicComplex (a n)
  simp only [← e]
  exact v5_broad_algebraic_arithmetic_map τ.toAlgHom _ ha

def v5BundledGaloisFactor (K : IntermediateField ℚ AlgebraicComplex) (a : ℕ → K)
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (σ : K ≃ₐ[ℚ] K) : subfieldEntireFunctionAlgebra k :=
  v5FactorialEntire (v5GaloisFactor K a σ)
    (v5_broad_series_hasSum_entire _ (v5_galois_factor_arithmetic K a ha σ)).1
    (fun n => (σ (a n) : AlgebraicComplex))
    (v5_broad_series_hasSum_entire _ (v5_galois_factor_arithmetic K a ha σ)).2

/-- The actual norm as the product in the same bundled entire algebra
expected by the checked quotient contradiction. -/
theorem v5_bundled_galois_norm_eq (K : IntermediateField ℚ AlgebraicComplex)
    [Fintype (K ≃ₐ[ℚ] K)] (a : ℕ → K)
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex))) :
    (∏ σ, v5BundledGaloisFactor K a ha σ).val.val = v5BroadGaloisNorm K a := by
  funext z
  change stage14_subfieldEntireEvaluation k z (∏ σ, v5BundledGaloisFactor K a ha σ) =
    ∏ σ, stage14_subfieldEntireEvaluation k z (v5BundledGaloisFactor K a ha σ)
  exact map_prod _ _ _

theorem v5_galois_factors_nonzero_of_norm (K : IntermediateField ℚ AlgebraicComplex)
    [Fintype (K ≃ₐ[ℚ] K)] (a : ℕ → K)
    (h : v5BroadGaloisNorm K a ≠ 0) (σ : K ≃ₐ[ℚ] K) :
    v5GaloisFactor K a σ ≠ 0 := by
  intro hz
  apply h
  funext z
  exact Finset.prod_eq_zero (Finset.mem_univ σ)
    (congrFun hz z)

/-- The vanishing norm of a nonzero broad function gives a nonzero actual
bundled product and the exact rational factorial data for its quotient. -/
theorem v5_bundled_galois_norm_data (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => ((a n : AlgebraicComplex) : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (hne : f ≠ 0) (hzero : f 1 = 0) :
    let G := ∏ σ, v5BundledGaloisFactor K a ha σ
    (∀ σ, v5GaloisFactor K a σ ≠ 0) ∧ G.val.val ≠ 0 ∧ G.val.val 1 = 0 ∧
      ∃ c : ℕ → AlgebraicComplex,
        (∀ z, HasSum (fun n => (c n : ℂ)*z^n/(n.factorial : ℂ)) (G.val.val z)) ∧
        HasAlgebraicPolynomialODE G.val.val ∧ V5BroadAlgebraicArithmetic c ∧
        ∀ n, ∃ q : ℚ, c n = algebraMap ℚ AlgebraicComplex q := by
  obtain ⟨⟨c,_,hcs,hco,hca,hcr⟩,hn,hz⟩ := v5_broad_galois_norm_properties K a f hf hs hODE ha
  dsimp only
  rw [v5_bundled_galois_norm_eq K a ha]
  exact ⟨v5_galois_factors_nonzero_of_norm K a (hn hne), hn hne, hz hzero, c,hcs,hco,hca,hcr⟩

#print axioms v5_galois_factor_arithmetic
#print axioms v5_bundled_galois_norm_eq
#print axioms v5_galois_factors_nonzero_of_norm
#print axioms v5_bundled_galois_norm_data
end StrictEUnit
