import V5ActualGaloisNormData
import V5ActualAlgebraicOrdinaryBlock

noncomputable section
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators Topology
namespace StrictEUnit
local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

theorem v5_algebraic_residual_eq_complex_mapped (f : ℂ → ℂ) (m : ℕ)
    (q : ℕ → Polynomial AlgebraicComplex) (z : ℂ) :
    v5RowResidual f m q z =
      v5RowResidual f m (fun j => (q j).map (algebraicClosure ℚ ℂ).val.toRingHom) z := by
  unfold v5RowResidual
  apply Finset.sum_congr rfl
  intro j _
  change (q j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * iteratedDeriv j f z =
    ((q j).map (algebraicClosure ℚ ℂ).val.toRingHom).eval z * iteratedDeriv j f z
  rw [Polynomial.eval_map]

/-- For a nonzero broad E-function vanishing at one, the actual rational
norm forces at least one analytic minimum-row family entirely to vanish. -/
theorem v5_actual_galois_vanishing_basis (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => ((a n : AlgebraicComplex) : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (ho : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (hne : f ≠ 0) (hzero : f 1 = 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ q : ℕ → Polynomial AlgebraicComplex,
      q m ≠ 0 ∧ (∀ z, v5RowResidual f m q z = 0) ∧
      ∃ σ : K ≃ₐ[ℚ] K, ∃ u : Fin m → ℂ → ℂ,
        (∀ i, AnalyticAt ℂ (u i) 1) ∧ v5FiniteGermIndependent (1 : ℂ) u ∧
        (∀ i, ∀ᶠ z in 𝓝 (1 : ℂ),
          v5RowResidual (u i) m (fun j => (q j).map (σ.liftNormal AlgebraicComplex).toRingHom) z = 0) ∧
        ∀ i, u i 1 = 0 := by
  classical
  let F := v5FactorialEntire f hf (fun n => (a n : AlgebraicComplex)) hs
  have hFne : F ≠ 0 := by
    intro h
    exact hne (congrArg (fun G : subfieldEntireFunctionAlgebra k => G.val.val) h)
  have hFb : V5IsBroadEFunction f := ⟨_,hf,hs,ho,ha⟩
  obtain ⟨n,P,_,hP,hPord⟩ := v5_actual_broad_annihilator_over_algebraic hFb hne
  have hPne : P n ≠ 0 := fun h => hPord 1 one_ne_zero (by rw [h,Polynomial.eval₂_zero])
  have hex : ∃ n, v5HasAnnihilatorOrder AlgebraicComplex f n := ⟨n,P,hPne,hP⟩
  let m := Nat.find hex
  obtain ⟨q,hq,hrow⟩ := Nat.find_spec hex
  change q m ≠ 0 at hq
  change ∀ z, v5RowResidual f m q z = 0 at hrow
  have hmin (l : ℕ) (hl : l < m) : ¬ v5HasAnnihilatorOrder AlgebraicComplex f l :=
    Nat.find_min hex hl
  have hm : 0 < m := by
    by_contra! h
    have he : m = 0 := Nat.eq_zero_of_le_zero h
    exact v5_actual_algebraic_no_order_zero F hFne (he ▸ (show
      v5HasAnnihilatorOrder AlgebraicComplex f m from ⟨q,hq,hrow⟩))
  let Fs := v5BundledGaloisFactor K a ha
  let G : subfieldEntireFunctionAlgebra k := ∏ σ, Fs σ
  obtain ⟨hgs,hGne,hGzero,c,hcs,hco,hca,hcr⟩ :=
    v5_bundled_galois_norm_data K a f hf hs ho ha hne hzero
  let Q := fun (σ : K ≃ₐ[ℚ] K) j => (q j).map (σ.liftNormal AlgebraicComplex).toRingHom
  have hall (σ : K ≃ₐ[ℚ] K) :
      ∃ u : Fin m → ℂ → ℂ,
        (∀ i, AnalyticAt ℂ (u i) 1) ∧ v5FiniteGermIndependent (1 : ℂ) u ∧
        ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (u i) m (Q σ) z = 0 :=
    v5_actual_galois_minimal_analytic_family K a σ f hf hs ho ha m q hq hrow hmin (hgs σ)
  choose us hua hui huo using hall
  by_cases hv : ∀ σ, ∃ i, us σ i 1 ≠ 0
  · exfalso
    have hb (σ : K ≃ₐ[ℚ] K) :
        ∃ d : Fin m → ℕ, ∃ i₀ : Fin m, d i₀ = 0 ∧
          ∃ (B : Matrix (Fin m) (Fin m) (RatFunc k)) (T : Polynomial k)
            (U : Matrix (Fin m) (Fin m) (Polynomial k)),
          let g := v5ActualEntireDerivativeCoordinates k (Fs σ) d
          T.eval 1 ≠ 0 ∧ g i₀ = Fs σ ∧
          LinearIndependent (RatFunc k) (fun i => v5ActualEntireLaurentAlgHom k (g i)) ∧
          (∀ i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (g i)) =
            ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B i j) *
              v5ActualEntireLaurentAlgHom k (g j)) ∧
          ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
            algebraMap (Polynomial k) (RatFunc k) T * B i j := by
      let τ := σ.liftNormal AlgebraicComplex
      have hQ : Q σ m ≠ 0 := (Polynomial.map_ne_zero_iff τ.injective).mpr hq
      have hrowσ : ∀ z, v5RowResidual (Fs σ).val.val m (Q σ) z = 0 := by
        apply (v5_actual_algebraic_row_residual _ _ _).mp
        exact (v5_actual_galois_scalar_row_iff K a σ f hf hs ha m (fun i => q i.val)).mp
          ((v5_actual_algebraic_row_residual f m q).mpr hrow)
      have hminσ (l : ℕ) (hl : l < m) :
          ¬ v5HasAnnihilatorOrder AlgebraicComplex (Fs σ).val.val l :=
        fun h => hmin l hl ((v5_actual_galois_annihilatorOrder_iff K a σ f hf hs ha l).mpr h)
      have hoσ (i : Fin m) : ∀ᶠ z in 𝓝 (1 : ℂ),
          v5RowResidual (us σ i) m
            (fun j => (Q σ j).map (algebraicClosure ℚ ℂ).val.toRingHom) z = 0 :=
        (huo σ i).mono (fun z hz => (v5_algebraic_residual_eq_complex_mapped _ _ _ z).symm.trans hz)
      exact v5_actual_algebraic_ordinary_jet_block hm (Q σ) hQ (Fs σ) hrowσ hminσ
        (us σ) (hua σ) (hui σ) hoσ (hv σ)
    choose d i₀ hd B T U hT hkeep hlin hsys hU using hb
    exact v5_broad_norm_ordinary_blocks_impossible Fs G rfl c hcs hco hca hcr hGzero hGne
      (fun σ => v5ActualEntireDerivativeCoordinates k (Fs σ) (d σ)) i₀ hkeep B T U hT hU hlin hsys
  · push_neg at hv
    obtain ⟨σ,hσ⟩ := hv
    exact ⟨m,hm,q,hq,hrow,σ,us σ,hua σ,hui σ,huo σ,hσ⟩

#print axioms v5_algebraic_residual_eq_complex_mapped
#print axioms v5_actual_galois_vanishing_basis
end StrictEUnit
