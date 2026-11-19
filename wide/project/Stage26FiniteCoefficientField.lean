import StrictEFunctionDefinitions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Order.Bounds.Basic

/-!
# Finite coefficient fields from genuine polynomial recurrences

This module isolates the elementary recurrence-to-number-field step. Its
hypothesis is a nonzero polynomial recurrence, not a prescribed coefficient
number field. Deriving this recurrence from a nonzero scalar differential
operator is a separate obligation.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A nonzero polynomial is nonvanishing on all sufficiently large natural
numbers, in any characteristic-zero field. -/
theorem stage26_polynomial_eventually_nat_nonzero {K : Type*} [Field K] [CharZero K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, p.eval (n : K) ≠ 0 := by
  have hfinite : Set.Finite {n : ℕ | p.eval (n : K) = 0} :=
    (Polynomial.finite_setOf_isRoot hp).preimage (Nat.cast_injective (R := K)).injOn
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  refine ⟨N + 1, ?_⟩
  intro n hn heq
  have := hN heq
  omega

/-- Polynomial evaluation remains in a field containing its coefficients. -/
theorem stage26_polynomial_eval_mem {K : Type*} [Field K] [Algebra ℚ K]
    (F : IntermediateField ℚ K) (p : Polynomial K)
    (hp : ∀ j, p.coeff j ∈ F) (n : ℕ) : p.eval (n : K) ∈ F := by
  rw [Polynomial.eval_eq_sum_range]
  exact F.sum_mem fun j _ => F.mul_mem (hp j) (pow_mem (F.natCast_mem n) j)

/-- A solved recurrence propagates membership in a fixed intermediate field,
including arbitrary exceptional initial indices. -/
theorem stage26_recurrence_mem {K : Type*} [Field K] [Algebra ℚ K]
    (F : IntermediateField ℚ K) (a : ℕ → K) (r N : ℕ)
    (q : Fin (r + 1) → Polynomial K)
    (hq : ∀ i j, (q i).coeff j ∈ F)
    (hlead : ∀ n ≥ N, (q (Fin.last r)).eval (n : K) ≠ 0)
    (hrec : ∀ n ≥ N, ∑ i, (q i).eval (n : K) * a (n + i.val) = 0)
    (hinit : ∀ j < N + r, a j ∈ F) :
    ∀ j, a j ∈ F := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j < N + r
    · exact hinit j hj
    · have hrj : r ≤ j := by omega
      have hNj : N ≤ j - r := by omega
      have hjr : j - r + r = j := Nat.sub_add_cancel hrj
      have hsum := hrec (j - r) hNj
      rw [Fin.sum_univ_castSucc] at hsum
      have hprev : (∑ i : Fin r,
          (q i.castSucc).eval ((j - r : ℕ) : K) * a (j - r + i.val)) ∈ F := by
        apply F.sum_mem
        intro i _
        apply F.mul_mem (stage26_polynomial_eval_mem F _ (hq i.castSucc) _)
        exact ih _ (by omega)
      have hsolve : a j = -(∑ i : Fin r,
          (q i.castSucc).eval ((j - r : ℕ) : K) * a (j - r + i.val)) /
          (q (Fin.last r)).eval ((j - r : ℕ) : K) := by
        apply (eq_div_iff (hlead _ hNj)).mpr
        simpa only [Fin.val_last, hjr, mul_comm] using (eq_neg_of_add_eq_zero_right hsum)
      rw [hsolve]
      exact F.div_mem (F.neg_mem hprev)
        (stage26_polynomial_eval_mem F _ (hq (Fin.last r)) _)

/-- A finite set of algebraic coefficients and initial values suffices for
any eventual polynomial recurrence with nonzero last coefficient. -/
theorem stage26_polynomial_recurrence_finite_coefficient_field
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (a : ℕ → K) (r : ℕ) (q : Fin (r + 1) → Polynomial K)
    (hq : q (Fin.last r) ≠ 0)
    (hrec : ∃ N : ℕ, ∀ n ≥ N, ∑ i, (q i).eval (n : K) * a (n + i.val) = 0) :
    ∃ F : IntermediateField ℚ K, FiniteDimensional ℚ F ∧
      (∀ j, a j ∈ F) ∧ (∀ i j, (q i).coeff j ∈ F) := by
  classical
  obtain ⟨N₀, hN₀⟩ := hrec
  obtain ⟨N₁, hN₁⟩ := stage26_polynomial_eventually_nat_nonzero _ hq
  let N := max N₀ N₁
  let S : Finset K := ((Finset.univ : Finset (Fin (r + 1))).biUnion
    fun i => (q i).support.image ((q i).coeff)) ∪ (Finset.range (N + r)).image a
  let F : IntermediateField ℚ K := IntermediateField.adjoin ℚ (S : Set K)
  have hcoeff : ∀ i j, (q i).coeff j ∈ F := by
    intro i j
    by_cases hj : j ∈ (q i).support
    · apply IntermediateField.subset_adjoin
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩)
    · simpa only [Polynomial.not_mem_support_iff.mp hj] using F.zero_mem
  have hinit : ∀ j < N + r, a j ∈ F := by
    intro j hj
    apply IntermediateField.subset_adjoin
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)
  refine ⟨F, ?_, ?_, hcoeff⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  · exact stage26_recurrence_mem F a r N q hcoeff
      (fun n hn => hN₁ n ((le_max_right _ _).trans hn))
      (fun n hn => hN₀ n ((le_max_left _ _).trans hn)) hinit

/-- A nonzero recurrence tuple need not have a nonzero final entry: trailing
zero entries can be removed without weakening the coefficient-field result. -/
theorem stage26_polynomial_recurrence_finite_coefficient_field_of_nonzero
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (a : ℕ → K) (r : ℕ) (q : Fin (r + 1) → Polynomial K)
    (hq : ∃ i, q i ≠ 0)
    (hrec : ∃ N : ℕ, ∀ n ≥ N, ∑ i, (q i).eval (n : K) * a (n + i.val) = 0) :
    ∃ F : IntermediateField ℚ K, FiniteDimensional ℚ F ∧
      (∀ j, a j ∈ F) ∧ (∀ i j, (q i).coeff j ∈ F) := by
  classical
  induction r with
  | zero =>
    apply stage26_polynomial_recurrence_finite_coefficient_field a 0 q _ hrec
    obtain ⟨i, hi⟩ := hq
    have hi0 : i = Fin.last 0 := Fin.ext (by omega)
    simpa only [hi0] using hi
  | succ r ih =>
    by_cases hlast : q (Fin.last (r + 1)) = 0
    · let q' : Fin (r + 1) → Polynomial K := fun i => q i.castSucc
      have hq' : ∃ i, q' i ≠ 0 := by
        obtain ⟨i, hi⟩ := hq
        refine Fin.lastCases ?_ (fun j hj => ⟨j, hj⟩) i hi
        simp [hlast]
      have hrec' : ∃ N : ℕ, ∀ n ≥ N,
          ∑ i, (q' i).eval (n : K) * a (n + i.val) = 0 := by
        obtain ⟨N, hN⟩ := hrec
        refine ⟨N, fun n hn => ?_⟩
        simpa [Fin.sum_univ_castSucc, hlast, q'] using hN n hn
      obtain ⟨F, hF, ha, hc⟩ := ih q' hq' hrec'
      refine ⟨F, hF, ha, ?_⟩
      intro i j
      refine Fin.lastCases ?_ (fun k => hc k j) i
      simpa [hlast] using F.zero_mem
    · exact stage26_polynomial_recurrence_finite_coefficient_field a (r + 1) q hlast hrec

/-- Finitely many algebraic polynomials have one common finite coefficient
field, and it may be chosen to contain any previously fixed number field. -/
theorem stage26_finite_coefficient_field_enlarge_polynomials
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    {ι : Type*} [Fintype ι] (F : IntermediateField ℚ K) (hF : FiniteDimensional ℚ F)
    (p : ι → Polynomial K) :
    ∃ E : IntermediateField ℚ K, FiniteDimensional ℚ E ∧ F ≤ E ∧
      ∀ i j, (p i).coeff j ∈ E := by
  classical
  let S : Finset K := Finset.univ.biUnion fun i => (p i).support.image ((p i).coeff)
  let G : IntermediateField ℚ K := IntermediateField.adjoin ℚ (S : Set K)
  letI : FiniteDimensional ℚ F := hF
  letI : FiniteDimensional ℚ G := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨F ⊔ G, inferInstance, le_sup_left, ?_⟩
  intro i j
  apply (show G ≤ F ⊔ G from le_sup_right)
  by_cases hj : j ∈ (p i).support
  · apply IntermediateField.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  · simpa only [Polynomial.not_mem_support_iff.mp hj] using G.zero_mem

/-- The recurrence theorem applies to the actual field of algebraic complex
numbers with no additional finiteness assumption. -/
theorem stage26_algebraic_recurrence_finite_coefficient_field
    (a : ℕ → AlgebraicComplex) (r : ℕ)
    (q : Fin (r + 1) → Polynomial AlgebraicComplex)
    (hq : q (Fin.last r) ≠ 0)
    (hrec : ∃ N : ℕ, ∀ n ≥ N,
      ∑ i, (q i).eval (n : AlgebraicComplex) * a (n + i.val) = 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex, FiniteDimensional ℚ F ∧
      (∀ j, a j ∈ F) ∧ (∀ i j, (q i).coeff j ∈ F) :=
  stage26_polynomial_recurrence_finite_coefficient_field a r q hq hrec

end StrictEUnit
