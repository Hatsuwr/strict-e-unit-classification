import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Preimage

/-!
# Finite resonance multiplicity budget

The shifts rho+n are distinct in characteristic zero. Their total root
multiplicity is bounded by the original symbol's degree, without any splitting
assumption. A final conditional degree estimate propagates this finite budget;
it does not construct a recurrence, a Frobenius basis or arithmetic bounds.
Source-only draft pending coordinated compiler verification.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Counting roots with multiplicity over any finite subset costs at most degree. -/
theorem polynomial_rootMultiplicity_sum_le (P : Polynomial K) (s : Finset K) :
    (∑ a ∈ s, P.rootMultiplicity a) ≤ P.natDegree := by
  classical
  simp_rw [← Polynomial.count_roots]
  calc
    (∑ a ∈ s, P.roots.count a) ≤
        ∑ a ∈ s ∪ P.roots.toFinset, P.roots.count a :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = P.roots.card := Multiset.sum_count_eq_card (by
      intro a ha
      exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- Any injective indexing retains the same multiplicity budget. -/
theorem polynomial_rootMultiplicity_sum_injective_le {ι : Type*}
    (P : Polynomial K) (s : Finset ι) (f : ι → K) (hf : Function.Injective f) :
    (∑ i ∈ s, P.rootMultiplicity (f i)) ≤ P.natDegree := by
  classical
  have hi : (∑ a ∈ s.image f, P.rootMultiplicity a) =
      ∑ i ∈ s, P.rootMultiplicity (f i) :=
    Finset.sum_image (fun i _ j _ hij => hf hij)
  rw [← hi]
  exact polynomial_rootMultiplicity_sum_le P _

section CharZero
variable [CharZero K]

/-- Characteristic zero prevents repeated shifts from counting a root twice. -/
theorem polynomialResonance_shift_injective (rho : K) :
    Function.Injective (fun n : ℕ => rho + (n : K)) := by
  intro m n h
  exact Nat.cast_injective (add_left_cancel h)

/-- Exact resonance multiplicity at the nth shifted exponent. -/
def polynomialResonanceMultiplicity (rho : K) (P : Polynomial K) (n : ℕ) : ℕ :=
  P.rootMultiplicity (rho + (n : K))

/-- The actual finite set of indices with positive resonance multiplicity. -/
def polynomialResonanceIndices (rho : K) (P : Polynomial K) : Finset ℕ := by
  classical
  exact P.roots.toFinset.preimage (fun n : ℕ => rho + (n : K))
    (polynomialResonance_shift_injective rho).injOn

@[simp] theorem polynomialResonanceIndices_mem (rho : K) (P : Polynomial K) (n : ℕ) :
    n ∈ polynomialResonanceIndices rho P ↔ polynomialResonanceMultiplicity rho P n ≠ 0 := by
  classical
  simp only [polynomialResonanceIndices, Finset.mem_preimage, Multiset.mem_toFinset,
    ← Multiset.count_pos, Polynomial.count_roots, Nat.pos_iff_ne_zero,
    polynomialResonanceMultiplicity]

/-- For a nonzero symbol, this is exactly the vanishing condition P(rho+n)=0. -/
theorem polynomialResonanceIndices_mem_iff_eval_zero (rho : K) (P : Polynomial K)
    (hP : P ≠ 0) (n : ℕ) :
    n ∈ polynomialResonanceIndices rho P ↔ P.eval (rho + (n : K)) = 0 := by
  rw [polynomialResonanceIndices_mem, polynomialResonanceMultiplicity,
    ← Nat.pos_iff_ne_zero, Polynomial.rootMultiplicity_pos hP]
  rfl

/-- The multiplicity function is genuinely finitely supported. -/
theorem polynomialResonanceMultiplicity_finite_support (rho : K) (P : Polynomial K) :
    (Function.support (polynomialResonanceMultiplicity rho P)).Finite := by
  have heq : Function.support (polynomialResonanceMultiplicity rho P) =
      (polynomialResonanceIndices rho P : Set ℕ) := by
    ext n
    simp only [Function.mem_support, Finset.mem_coe, polynomialResonanceIndices_mem]
  rw [heq]
  exact (polynomialResonanceIndices rho P).finite_toSet

/-- The budget holds for any finite index set, including arbitrary initial segments. -/
theorem polynomialResonanceMultiplicity_sum_le (rho : K) (P : Polynomial K)
    (s : Finset ℕ) :
    (∑ n ∈ s, polynomialResonanceMultiplicity rho P n) ≤ P.natDegree :=
  polynomial_rootMultiplicity_sum_injective_le P s _
    (polynomialResonance_shift_injective rho)

def polynomialResonanceTotalCost (rho : K) (P : Polynomial K) : ℕ :=
  ∑ n ∈ polynomialResonanceIndices rho P, polynomialResonanceMultiplicity rho P n

theorem polynomialResonanceTotalCost_le (rho : K) (P : Polynomial K) :
    polynomialResonanceTotalCost rho P ≤ P.natDegree :=
  polynomialResonanceMultiplicity_sum_le rho P _

def polynomialResonancePrefixCost (rho : K) (P : Polynomial K) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, polynomialResonanceMultiplicity rho P n

theorem polynomialResonancePrefixCost_le (rho : K) (P : Polynomial K) (N : ℕ) :
    polynomialResonancePrefixCost rho P N ≤ P.natDegree :=
  polynomialResonanceMultiplicity_sum_le rho P _

/-- Beyond the largest resonant index every multiplicity is zero. -/
theorem polynomialResonanceMultiplicity_eventually_zero (rho : K) (P : Polynomial K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → polynomialResonanceMultiplicity rho P n = 0 := by
  refine ⟨(polynomialResonanceIndices rho P).sup id + 1, ?_⟩
  intro n hn
  by_contra hne
  have hmem := (polynomialResonanceIndices_mem rho P n).mpr hne
  have hle : n ≤ (polynomialResonanceIndices rho P).sup id := Finset.le_sup (f := id) hmem
  exact (Nat.not_succ_le_self _) (hn.trans hle)

/-- The zero-symbol edge case has no positive multiplicity by definition.
This does not identify its infinitely many vanishing values with resonances. -/
@[simp] theorem polynomialResonanceMultiplicity_zero (rho : K) (n : ℕ) :
    polynomialResonanceMultiplicity rho (0 : Polynomial K) n = 0 := by
  simp only [polynomialResonanceMultiplicity, Polynomial.rootMultiplicity_zero]

end CharZero

/-- Conditional propagation of a degree bound for a lower-triangular recurrence.
This is an inequality lemma only; no recurrence existence is assumed or asserted. -/
theorem nat_degree_budget_of_lower_triangular_bound (q d : ℕ → ℕ) (B : ℕ)
    (hstep : ∀ n, d n ≤ max B ((Finset.range n).sup d) + q n) (n : ℕ) :
    d n ≤ B + ∑ i ∈ Finset.range (n + 1), q i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hsup : (Finset.range n).sup d ≤ B + ∑ i ∈ Finset.range n, q i := by
      apply Finset.sup_le
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact (ih i hin).trans (Nat.add_le_add_left
        (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hin))) B)
    calc
      d n ≤ max B ((Finset.range n).sup d) + q n := hstep n
      _ ≤ (B + ∑ i ∈ Finset.range n, q i) + q n :=
        Nat.add_le_add_right (max_le (Nat.le_add_right _ _) hsup) _
      _ = B + ∑ i ∈ Finset.range (n + 1), q i := by
        rw [Finset.sum_range_succ, Nat.add_assoc]

/-- The finite resonance budget yields one global log-degree bound once the
actual recurrence has supplied the displayed lower-triangular inequality. -/
theorem polynomialResonance_uniform_degree_bound [CharZero K]
    (rho : K) (P : Polynomial K) (d : ℕ → ℕ) (B : ℕ)
    (hstep : ∀ n, d n ≤ max B ((Finset.range n).sup d) +
      polynomialResonanceMultiplicity rho P n) (n : ℕ) :
    d n ≤ B + P.natDegree :=
  (nat_degree_budget_of_lower_triangular_bound _ d B hstep n).trans
    (Nat.add_le_add_left (polynomialResonanceMultiplicity_sum_le rho P _) B)

end StrictEUnit
