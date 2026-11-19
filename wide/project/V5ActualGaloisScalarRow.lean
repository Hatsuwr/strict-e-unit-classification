import V5BroadGaloisNorm
import V5ScalarJetTransport
import V5AffineMinimumOrder

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace StrictEUnit

def v5ActualAlgebraicRow (f : ℂ → ℂ) (m : ℕ)
    (p : Fin (m+1) → Polynomial AlgebraicComplex) : Prop :=
  ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
    iteratedDeriv i.val f z = 0

def v5FactorialSeries (a : ℕ → AlgebraicComplex) : PowerSeries AlgebraicComplex :=
  PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))

/-- Actual row and formal row are equivalent for the same tuple and order. -/
theorem v5_actual_algebraic_row_iff_factorial (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex) :
    v5ActualAlgebraicRow f m p ↔
      ∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val] (v5FactorialSeries a) = 0 := by
  constructor
  · intro h
    exact (v5_actual_broad_ode_data ⟨f,hf⟩ a hs m p h).2
  · intro h
    let φ := (algebraicClosure ℚ ℂ).val.toRingHom
    let F : entireFunctionAlgebra := ⟨f,hf⟩
    let P : ℕ → Polynomial ℂ := fun j => if hj : j < m+1 then (p ⟨j,hj⟩).map φ else 0
    have hP (i : Fin (m+1)) : P i.val = (p i).map φ := dif_pos i.isLt
    have hx : PowerSeries.map φ (v5FactorialSeries a) = entireTaylorAlgHom F := by
      ext n
      rw [entireTaylorAlgHom_apply, coeff_entireFormalTaylor]
      have ht := v5_factorial_series_cauchyCoefficient f hf a hs n
      simp only [v5FactorialSeries, PowerSeries.coeff_map, PowerSeries.coeff_mk,
        map_div₀, map_natCast]
      exact ht.symm
    have he := congrArg (PowerSeries.map φ) h
    rw [map_sum,map_zero] at he
    simp only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe, hx] at he
    have hr : v5FormalRow P m (entireTaylorAlgHom F) = 0 := by
      rw [v5FormalRow, ← Fin.sum_univ_eq_sum_range]
      simpa only [hP] using he
    intro z
    have hres := (v5_formalRow_eq_zero_iff F P m).mp hr z
    rw [v5RowResidual, ← Fin.sum_univ_eq_sum_range] at hres
    change (∑ i : Fin (m+1), (P i.val).eval z * iteratedDeriv i.val f z) = 0 at hres
    simpa only [hP, Polynomial.eval_map] using hres

theorem v5_factorial_row_map_iff (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex) :
    (∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val] (v5FactorialSeries a) = 0) ↔
    (∑ i, ((p i).map σ.toRingHom : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val] (v5FactorialSeries (fun n => σ (a n))) = 0) := by
  rw [← (PowerSeries.map_injective σ.toRingHom σ.injective).eq_iff, map_sum, map_zero]
  simp only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe,
    v5FactorialSeries, v5_factorial_series_map]
  rfl

/-- Actual norm factor satisfies exactly the mapped scalar rows, conversely as well. -/
theorem v5_actual_galois_scalar_row_iff (K : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → K) (σ : K ≃ₐ[ℚ] K) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => ((a n : AlgebraicComplex) : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex) :
    v5ActualAlgebraicRow f m p ↔
      v5ActualAlgebraicRow
        (exponentialGeneratingFunction (fun n => ((σ (a n) : AlgebraicComplex) : ℂ))) m
        (fun i => (p i).map (σ.liftNormal AlgebraicComplex).toRingHom) := by
  let τ := σ.liftNormal AlgebraicComplex
  have he (n : ℕ) : τ (a n : AlgebraicComplex) = (σ (a n) : AlgebraicComplex) :=
    σ.liftNormal_commutes AlgebraicComplex (a n)
  have hca : V5BroadAlgebraicArithmetic (fun n => (σ (a n) : AlgebraicComplex)) := by
    simp only [← he]
    exact v5_broad_algebraic_arithmetic_map τ.toAlgHom _ ha
  obtain ⟨hd,hg⟩ := v5_broad_series_hasSum_entire _ hca
  rw [v5_actual_algebraic_row_iff_factorial f hf _ hs,
    v5_actual_algebraic_row_iff_factorial _ hd _ hg]
  simpa only [τ, ← he] using v5_factorial_row_map_iff τ (fun n => (a n : AlgebraicComplex)) m p

theorem v5_algebraic_annihilatorOrder_iff (f : ℂ → ℂ) (m : ℕ) :
    v5HasAnnihilatorOrder AlgebraicComplex f m ↔
      ∃ p : Fin (m+1) → Polynomial AlgebraicComplex,
        p (Fin.last m) ≠ 0 ∧ v5ActualAlgebraicRow f m p := by
  constructor
  · rintro ⟨p,hp,h⟩
    refine ⟨fun i => p i.val,hp,?_⟩
    intro z
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (p j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * iteratedDeriv j f z)]
    exact h z
  · rintro ⟨p,hp,h⟩
    let P : ℕ → Polynomial AlgebraicComplex := fun j =>
      if hj : j < m+1 then p ⟨j,hj⟩ else 0
    have hP (i : Fin (m+1)) : P i.val = p i := dif_pos i.isLt
    refine ⟨P, by simpa only [← hP (Fin.last m)] using hp, ?_⟩
    intro z
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hP]
    exact h z

/-- The set of actual annihilator orders is preserved, not just existence
of some annihilator. In particular, conjugating a minimum row keeps it minimum. -/
theorem v5_actual_galois_annihilatorOrder_iff (K : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → K) (σ : K ≃ₐ[ℚ] K) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => ((a n : AlgebraicComplex) : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (m : ℕ) :
    v5HasAnnihilatorOrder AlgebraicComplex f m ↔
      v5HasAnnihilatorOrder AlgebraicComplex
        (exponentialGeneratingFunction (fun n => ((σ (a n) : AlgebraicComplex) : ℂ))) m := by
  rw [v5_algebraic_annihilatorOrder_iff, v5_algebraic_annihilatorOrder_iff]
  let τ := σ.liftNormal AlgebraicComplex
  have hτ (q : Polynomial AlgebraicComplex) :
      (q.map τ.symm.toRingHom).map τ.toRingHom = q := by
    rw [Polynomial.map_map]
    have hm : τ.toRingHom.comp τ.symm.toRingHom = RingHom.id AlgebraicComplex := by
      apply RingHom.ext
      intro x
      change τ (τ.symm x) = x
      exact τ.apply_symm_apply x
    rw [hm,Polynomial.map_id]
  constructor
  · rintro ⟨p,hp,hr⟩
    refine ⟨fun i => (p i).map τ.toRingHom,
      (Polynomial.map_ne_zero_iff τ.injective).mpr hp,?_⟩
    exact (v5_actual_galois_scalar_row_iff K a σ f hf hs ha m p).mp hr
  · rintro ⟨p,hp,hr⟩
    let q := fun i : Fin (m+1) => (p i).map τ.symm.toRingHom
    refine ⟨q,(Polynomial.map_ne_zero_iff τ.symm.injective).mpr hp,?_⟩
    apply (v5_actual_galois_scalar_row_iff K a σ f hf hs ha m q).mpr
    change v5ActualAlgebraicRow _ m (fun i => ((p i).map τ.symm.toRingHom).map τ.toRingHom)
    simpa only [hτ] using hr

#print axioms v5_actual_algebraic_row_iff_factorial
#print axioms v5_factorial_row_map_iff
#print axioms v5_actual_galois_scalar_row_iff
#print axioms v5_algebraic_annihilatorOrder_iff
#print axioms v5_actual_galois_annihilatorOrder_iff
end StrictEUnit
