import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
New reconstruction, not recovered original source.
A continuous polynomial-growth majorant for the roots of a monic polynomial
whose coefficients are polynomials in the parameter. No analytic assumption
or desired conclusion is introduced as a placeholder.
-/
noncomputable section
open scoped BigOperators
open Polynomial

namespace StrictEUnit

/-- A convenient, deliberately non-sharp version of Cauchy's root bound. -/
theorem monic_root_norm_le_coeff_sum {q : Polynomial ℂ} (hq : q.Monic)
    {w : ℂ} (hw : q.eval w = 0) :
    ‖w‖ ≤ (∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖) + 1 := by
  have hs : (Finset.range q.natDegree).sup (fun i => ‖q.coeff i‖₊) ≤
      ∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖₊ := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum
      (s := Finset.range (q.natDegree + 1))
      (f := fun j : ℕ => ‖q.coeff j‖₊)
      (fun j hj => zero_le _) 
      (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self _)))
  have hb : q.cauchyBound ≤
      (∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖₊) + 1 := by
    simpa only [Polynomial.cauchyBound, show q.leadingCoeff = 1 from hq,
      nnnorm_one, div_one] using add_le_add_right hs (1 : NNReal)
  have hr := (Polynomial.IsRoot.norm_lt_cauchyBound hq.ne_zero hw).le.trans hb
  have hrReal := NNReal.coe_le_coe.mpr hr
  simpa only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_one, coe_nnnorm] using hrReal

/-- Sum-of-coefficient bound for evaluating one polynomial outside the unit disk. -/
theorem polynomial_eval_norm_le_coeff_sum_mul_pow (q : Polynomial ℂ) (N : ℕ)
    (hN : q.natDegree ≤ N) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖q.eval z‖ ≤
      (∑ j ∈ Finset.range (q.natDegree + 1), ‖q.coeff j‖) * ‖z‖ ^ N := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * z ^ j‖
      ≤ ∑ j ∈ Finset.range (q.natDegree + 1), ‖q.coeff j * z ^ j‖ :=
        norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (q.natDegree + 1), ‖q.coeff j‖ * ‖z‖ ^ j := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ j ∈ Finset.range (q.natDegree + 1), ‖q.coeff j‖ * ‖z‖ ^ N := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_right₀ hz
        ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hN)
    _ = (∑ j ∈ Finset.range (q.natDegree + 1), ‖q.coeff j‖) * ‖z‖ ^ N := by
      rw [Finset.sum_mul]

/-- A continuous majorant, including the harmless leading coefficient. -/
def monicRootEnvelope (p : Polynomial (Polynomial ℂ)) (z : ℂ) : ℝ :=
  (∑ i ∈ Finset.range (p.natDegree + 1), ‖(p.coeff i).eval z‖) + 1

lemma monicRootEnvelope_nonneg (p : Polynomial (Polynomial ℂ)) (z : ℂ) :
    0 ≤ monicRootEnvelope p z := by
  unfold monicRootEnvelope
  positivity

lemma continuous_monicRootEnvelope (p : Polynomial (Polynomial ℂ)) :
    Continuous (monicRootEnvelope p) := by
  unfold monicRootEnvelope
  exact (continuous_finset_sum _ (fun i hi => (p.coeff i).continuous.norm)).add
    continuous_const

lemma norm_le_monicRootEnvelope {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    {z w : ℂ} (hw : (p.map (Polynomial.evalRingHom z)).eval w = 0) :
    ‖w‖ ≤ monicRootEnvelope p z := by
  have h := monic_root_norm_le_coeff_sum (hp.map (Polynomial.evalRingHom z)) hw
  simpa only [monicRootEnvelope, hp.natDegree_map, Polynomial.coeff_map,
    Polynomial.coe_evalRingHom] using h

/-- This bound includes zeros of G: the total quotient is zero there. -/
lemma quotient_norm_le_monicRootEnvelope {F G : ℂ → ℂ}
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (hroot : ∀ z, G z ≠ 0 → (p.map (Polynomial.evalRingHom z)).eval (F z / G z) = 0)
    (z : ℂ) : ‖F z / G z‖ ≤ monicRootEnvelope p z := by
  by_cases hz : G z = 0
  · simpa only [hz, div_zero, norm_zero] using monicRootEnvelope_nonneg p z
  · exact norm_le_monicRootEnvelope hp (hroot z hz)

/-- The envelope has actual polynomial growth, with constants derived from p. -/
theorem monicRootEnvelope_polynomial_growth (p : Polynomial (Polynomial ℂ)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ z : ℂ, 1 ≤ ‖z‖ → monicRootEnvelope p z ≤ C * ‖z‖ ^ N + C := by
  classical
  let s := Finset.range (p.natDegree + 1)
  let N := s.sup (fun i => (p.coeff i).natDegree)
  let A : ℝ := ∑ i ∈ s,
    ∑ j ∈ Finset.range ((p.coeff i).natDegree + 1), ‖(p.coeff i).coeff j‖
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A + 1, N, by positivity, ?_⟩
  intro z hz
  have hs : (∑ i ∈ s, ‖(p.coeff i).eval z‖) ≤ A * ‖z‖ ^ N := by
    dsimp [A]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    exact polynomial_eval_norm_le_coeff_sum_mul_pow (p.coeff i) N
      (Finset.le_sup (f := fun j : ℕ => (p.coeff j).natDegree) hi) hz
  change (∑ i ∈ s, ‖(p.coeff i).eval z‖) + 1 ≤ _
  have hpow : 0 ≤ ‖z‖ ^ N := pow_nonneg (norm_nonneg _) _
  nlinarith

end StrictEUnit

#print axioms StrictEUnit.monic_root_norm_le_coeff_sum
#print axioms StrictEUnit.polynomial_eval_norm_le_coeff_sum_mul_pow
#print axioms StrictEUnit.monicRootEnvelope_polynomial_growth
