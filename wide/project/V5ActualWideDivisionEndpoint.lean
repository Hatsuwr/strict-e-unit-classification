import V5ActualGaloisVanishingBasis
import V5ActualWideEmbeddingVanishing
import V5BroadDivisionAtOne

noncomputable section
set_option maxHeartbeats 2500000
open scoped BigOperators Topology
namespace StrictEUnit

/-- Any zero at one of a nonzero broad function has all its algebraic
coefficient-conjugate evaluations zero there. The normal field and the
independent analytic family are constructed, not supplied. -/
theorem v5_actual_wide_conjugate_vanishing_at_one
    (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic a)
    (hne : f ≠ 0) (hzero : f 1 = 0) :
    ∀ ψ : AlgebraicComplex →ₐ[ℚ] ℂ,
      HasSum (fun n => ψ (a n)/(n.factorial : ℂ)) 0 := by
  obtain ⟨r,p,hp,hr⟩ := hODE
  have hformal := (v5_actual_broad_ode_data ⟨f,hf⟩ a hs r p hr).2
  obtain ⟨E,hmem,_,hE,_,_,_⟩ := v5_broad_factorial_ode_descends a r p hp hformal
  letI : FiniteDimensional ℚ E := hE
  let K : IntermediateField ℚ AlgebraicComplex :=
    IntermediateField.normalClosure ℚ E AlgebraicComplex
  letI : FiniteDimensional ℚ K := inferInstance
  letI : IsGalois ℚ K := inferInstance
  letI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  let b : ℕ → K := fun n => ⟨a n, IntermediateField.le_normalClosure E (hmem n)⟩
  obtain ⟨m,hm,q,hq,hrow,σ,u,hu,hi,hou,hzu⟩ :=
    v5_actual_galois_vanishing_basis K b f hf hs ⟨r,p,hp,hr⟩ ha hne hzero
  exact v5_actual_wide_embedding_vanishing f a hf hs ha m hm q hq hrow
    (σ.liftNormal AlgebraicComplex) u hu hi hou hzu

/-- Closure of the actual broad E-function class under division by 1-z
when its value at one is zero. No rationality or conjugate-zero assumption. -/
theorem v5_actual_wide_division_at_one {f : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) (hzero : f 1 = 0) :
    ∃ g : ℂ → ℂ, V5IsBroadEFunction g ∧ ∀ z, (1-z)*g z = f z := by
  by_cases hn : f = 0
  · exact ⟨f,hf,by simp [hn]⟩
  obtain ⟨a,hd,hs,ho,ha⟩ := hf
  exact v5_broad_division_at_one f a hd hs ho ha
    (v5_actual_wide_conjugate_vanishing_at_one f a hd hs ho ha hn hzero)

#print axioms v5_actual_wide_conjugate_vanishing_at_one
#print axioms v5_actual_wide_division_at_one
end StrictEUnit
