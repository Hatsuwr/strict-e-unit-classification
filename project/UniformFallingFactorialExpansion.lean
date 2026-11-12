import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Max

/-!
# One finite falling-factorial bound for a finite polynomial family

NEW SOURCE-ONLY helper. No compiler or kernel check has run on this file.
The monic polynomial sequence descPochhammer K n is a genuine K-basis of K[X].
Its repr coordinates have finite support. A single supremum over all those
supports gives a common finite index, and zeros pad each expansion to that
index. No degree bound, nonzero polynomial, uniqueness or characteristic-zero
hypothesis is supplied. The zero family is included without a separate case.
This is an algebraic expansion only, not a recurrence or arithmetic theorem.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- Every finite polynomial family has an expansion in descending Pochhammer
polynomials with one common finite coefficient range. -/
theorem exists_uniform_descPochhammer_expansion
    {K : Type*} [Field K] (r : ℕ) (H : Fin (r + 1) → Polynomial K) :
    ∃ L : ℕ, ∃ b : Fin (r + 1) → Fin (L + 1) → K,
      ∀ j, H j = ∑ t : Fin (L + 1),
        Polynomial.C (b j t) * descPochhammer K t.val := by
  let S : Polynomial.Sequence K := {
    elems' := descPochhammer K
    degree_eq' := fun n => by
      rw [Polynomial.degree_eq_natDegree (monic_descPochhammer K n).ne_zero,
        descPochhammer_natDegree] }
  have hunit (n : ℕ) : IsUnit (S n).leadingCoeff := by
    change IsUnit (descPochhammer K n).leadingCoeff
    rw [(monic_descPochhammer K n).leadingCoeff]
    exact isUnit_one
  let B : Basis ℕ K (Polynomial K) := S.basis hunit
  have hB (n : ℕ) : B n = descPochhammer K n := S.basis_eq_self hunit n
  let f : Fin (r + 1) → ℕ →₀ K := fun j => B.repr (H j)
  let L : ℕ := Finset.univ.sup (fun j : Fin (r + 1) => (f j).support.sup id)
  have hsupp (j : Fin (r + 1)) : (f j).support ⊆ Finset.range (L + 1) := by
    intro n hn
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    have hn' : n ≤ (f j).support.sup id := Finset.le_sup (f := id) hn
    have hj : (f j).support.sup id ≤ L :=
      Finset.le_sup (f := fun j : Fin (r + 1) => (f j).support.sup id)
        (Finset.mem_univ j)
    exact hn'.trans hj
  refine ⟨L, (fun j t => f j t.val), ?_⟩
  intro j
  have hrepr : (f j).sum (fun n a => a • B n) = H j := by
    change Finsupp.linearCombination K B (B.repr (H j)) = H j
    exact B.linearCombination_repr (H j)
  calc
    H j = (f j).sum (fun n a => a • B n) := hrepr.symm
    _ = ∑ n ∈ Finset.range (L + 1), f j n • B n :=
      Finsupp.sum_of_support_subset (f j) (hsupp j)
        (fun n a => a • B n) (fun n _ => zero_smul K (B n))
    _ = ∑ t : Fin (L + 1), f j t.val • B t.val :=
      (Fin.sum_univ_eq_sum_range (fun n => f j n • B n) (L + 1)).symm
    _ = ∑ t : Fin (L + 1), Polynomial.C (f j t.val) * descPochhammer K t.val := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hB, Polynomial.smul_eq_C_mul]

end StrictEUnit
end

#print axioms StrictEUnit.exists_uniform_descPochhammer_expansion
