import LaurentLogSimplicity
import Mathlib.Algebra.Polynomial.Laurent

/-! Actual finite Laurent-mode operator with polynomial logarithmic
coefficients. Leibniz is a separate obligation until explicitly proved. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]
variable (c : k)

/-- The shifted logarithmic Euler operator, coefficientwise
p_n ↦ p_n' + (c*n-a)p_n. -/
def scaledLaurentLogShift (a : k) :
    LaurentPolynomial (Polynomial k) →ₗ[k] LaurentPolynomial (Polynomial k) where
  toFun f := Finsupp.onFinset f.support
    (fun n => shiftedPolynomialDerivative (c * (n : k) - a) (f n))
    (by
      intro n hn
      apply Finsupp.mem_support_iff.mpr
      intro hz
      exact hn (by simp only [hz, map_zero]))
  map_add' f g := by
    apply Finsupp.ext
    intro n
    exact map_add (shiftedPolynomialDerivative (c * (n : k) - a)) (f n) (g n)
  map_smul' b f := by
    apply Finsupp.ext
    intro n
    exact map_smul (shiftedPolynomialDerivative (c * (n : k) - a)) b (f n)

/-- The unshifted operator. -/
def scaledLaurentLogD : LaurentPolynomial (Polynomial k) →ₗ[k] LaurentPolynomial (Polynomial k) :=
  scaledLaurentLogShift c 0

@[simp] theorem scaledLaurentLogShift_coeff (a : k)
    (f : LaurentPolynomial (Polynomial k)) (n : ℤ) :
    scaledLaurentLogShift c a f n = shiftedPolynomialDerivative (c * (n : k) - a) (f n) := rfl

@[simp] theorem scaledLaurentLogD_coeff (f : LaurentPolynomial (Polynomial k)) (n : ℤ) :
    scaledLaurentLogD c f n = (f n).derivative + (c * (n : k)) • f n := by
  simp [scaledLaurentLogD, shiftedPolynomialDerivative_apply]

theorem scaledLaurentLogShift_eq (a : k) (f : LaurentPolynomial (Polynomial k)) :
    scaledLaurentLogShift c a f = scaledLaurentLogD c f - a • f := by
  apply Finsupp.ext
  intro n
  change (f n).derivative + (c * (n : k) - a) • f n =
    (f n).derivative + (c * (n : k) - 0) • f n - a • f n
  rw [sub_zero, sub_smul, add_sub_assoc]

theorem scaledLaurentLogShift_iterate_coeff (a : k)
    (f : LaurentPolynomial (Polynomial k)) (n : ℤ) (j : ℕ) :
    (scaledLaurentLogShift c a)^[j] f n =
      (shiftedPolynomialDerivative (c * (n : k) - a))^[j] (f n) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', scaledLaurentLogShift_coeff, ih,
      Function.iterate_succ_apply']

theorem scaledLaurentLogShift_iterate_support_subset (a : k)
    (f : LaurentPolynomial (Polynomial k)) (j : ℕ) :
    ((scaledLaurentLogShift c a)^[j] f).support ⊆ f.support := by
  intro n hn
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have he := Finsupp.mem_support_iff.mp hn
  rw [scaledLaurentLogShift_iterate_coeff, hz, iterate_map_zero] at he
  exact he rfl

theorem scaledLaurentLogShift_stable_ideal
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, scaledLaurentLogD c f ∈ I) (a : k)
    (f : LaurentPolynomial (Polynomial k)) (hf : f ∈ I) (j : ℕ) :
    (scaledLaurentLogShift c a)^[j] f ∈ I := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply', scaledLaurentLogShift_eq]
    apply I.sub_mem (hI _ ih)
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ ih

variable [CharZero k] (hcscale : c ≠ 0)
include hcscale
/-- A minimal-support nonzero stable-ideal element has only one Laurent mode. -/
theorem scaledLaurentLog_minimal_support_single
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, scaledLaurentLogD c f ∈ I)
    (f : LaurentPolynomial (Polynomial k)) (hf : f ∈ I) (hf0 : f ≠ 0)
    (hmin : ∀ g ∈ I, g ≠ 0 → f.support.card ≤ g.support.card) :
    ∃ n : ℤ, f.support ⊆ {n} := by
  obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hf0
  refine ⟨n, ?_⟩
  intro m hm
  apply Finset.mem_singleton.mpr
  by_contra hmn
  let j := (f n).natDegree + 1
  let g := (scaledLaurentLogShift c (c * (n : k)))^[j] f
  have hgI : g ∈ I := scaledLaurentLogShift_stable_ideal c I hI _ f hf j
  have hgn : g n = 0 := by
    rw [scaledLaurentLogShift_iterate_coeff, sub_self]
    rw [show shiftedPolynomialDerivative (0 : k) = Polynomial.derivative by
      simp [shiftedPolynomialDerivative]]
    exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)
  have hgm : g m ≠ 0 := by
    rw [scaledLaurentLogShift_iterate_coeff]
    apply shiftedPolynomialDerivative_iterate_ne_zero _ _ _ (Finsupp.mem_support_iff.mp hm)
    apply sub_ne_zero.mpr
    intro heq
    have heq' : (m : k) = (n : k) := mul_left_cancel₀ hcscale heq
    exact hmn (by exact_mod_cast heq')
  have hg0 : g ≠ 0 := by intro h; apply hgm; rw [h]; rfl
  have hsub : g.support ⊆ f.support.erase n := by
    intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, scaledLaurentLogShift_iterate_support_subset c (c * (n : k)) f j hi⟩
    intro hin
    subst i
    exact Finsupp.mem_support_iff.mp hi hgn
  have hlt : g.support.card < f.support.card :=
    lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hn)
  exact (Nat.not_lt_of_ge (hmin g hgI hg0)) hlt

/-- Every nonzero stable ideal contains a nonzero single Laurent mode. -/
theorem scaledLaurentLog_stable_contains_single
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, scaledLaurentLogD c f ∈ I) (hI0 : I ≠ ⊥) :
    ∃ n : ℤ, ∃ p : Polynomial k, p ≠ 0 ∧ Finsupp.single n p ∈ I := by
  obtain ⟨f, hfI, hf0⟩ := (Submodule.ne_bot_iff I).mp hI0
  obtain ⟨g, ⟨hgI, hg0⟩, hmin⟩ :=
    (measure (fun f : LaurentPolynomial (Polynomial k) => f.support.card)).wf.has_min
      {f | f ∈ I ∧ f ≠ 0} ⟨f, hfI, hf0⟩
  obtain ⟨n, hn⟩ := scaledLaurentLog_minimal_support_single c hcscale I hI g hgI hg0
    (by intro h hh hh0; exact Nat.le_of_not_lt (hmin h ⟨hh, hh0⟩))
  have he : g = Finsupp.single n (g n) := Finsupp.support_subset_singleton.mp hn
  refine ⟨n, g n, ?_, he ▸ hgI⟩
  intro hz
  apply hg0
  rw [he, hz, Finsupp.single_zero]

/-- The actual Laurent-plus-logarithm operator has no nontrivial stable ideals. -/
theorem scaledLaurentLog_stable_ideal_eq_top
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, scaledLaurentLogD c f ∈ I) (hI0 : I ≠ ⊥) : I = ⊤ := by
  obtain ⟨n, p, hp, hnp⟩ := scaledLaurentLog_stable_contains_single c hcscale I hI hI0
  obtain ⟨d, hd, hpc⟩ := polynomial_top_derivative_constant p hp
  have hg := scaledLaurentLogShift_stable_ideal c I hI (c * (n : k))
    (Finsupp.single n p) hnp p.natDegree
  have he : (scaledLaurentLogShift c (c * (n : k)))^[p.natDegree] (Finsupp.single n p) =
      Finsupp.single n (Polynomial.C d) := by
    apply Finsupp.ext
    intro m
    rw [scaledLaurentLogShift_iterate_coeff]
    by_cases hmn : m = n
    · subst m
      simp only [Finsupp.single_eq_same, sub_self]
      rw [show shiftedPolynomialDerivative (0 : k) = Polynomial.derivative by
        simp [shiftedPolynomialDerivative]]
      exact hpc
    · simp only [Finsupp.single_eq_of_ne (Ne.symm hmn), iterate_map_zero]
  rw [he] at hg
  apply Ideal.eq_top_of_isUnit_mem I hg
  apply isUnit_of_mul_eq_one (M := LaurentPolynomial (Polynomial k))
    (Finsupp.single n (Polynomial.C d) : LaurentPolynomial (Polynomial k))
    (Finsupp.single (-n) (Polynomial.C d⁻¹) : LaurentPolynomial (Polynomial k))
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, ← Polynomial.C_mul,
    mul_inv_cancel₀ hd, Polynomial.C_1]
  exact AddMonoidAlgebra.one_def.symm


omit hcscale in
/-- In particular, the manuscript scale 1/N is simple for every N≥1. -/
theorem manuscriptLaurentLog_stable_ideal_eq_top
    (N : ℕ) (hN : N ≠ 0)
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, scaledLaurentLogD (N : k)⁻¹ f ∈ I)
    (hI0 : I ≠ ⊥) : I = ⊤ :=
  scaledLaurentLog_stable_ideal_eq_top (N : k)⁻¹
    (inv_ne_zero (Nat.cast_ne_zero.mpr hN)) I hI hI0

end StrictEUnit

#print axioms StrictEUnit.scaledLaurentLogShift
#print axioms StrictEUnit.scaledLaurentLogD
#print axioms StrictEUnit.scaledLaurentLogShift_coeff
#print axioms StrictEUnit.scaledLaurentLogD_coeff
#print axioms StrictEUnit.scaledLaurentLogShift_eq
#print axioms StrictEUnit.scaledLaurentLogShift_iterate_coeff
#print axioms StrictEUnit.scaledLaurentLogShift_iterate_support_subset
#print axioms StrictEUnit.scaledLaurentLogShift_stable_ideal
#print axioms StrictEUnit.scaledLaurentLog_minimal_support_single
#print axioms StrictEUnit.scaledLaurentLog_stable_contains_single
#print axioms StrictEUnit.scaledLaurentLog_stable_ideal_eq_top
#print axioms StrictEUnit.manuscriptLaurentLog_stable_ideal_eq_top
