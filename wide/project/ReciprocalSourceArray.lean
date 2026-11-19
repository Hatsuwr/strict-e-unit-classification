import ReciprocalGaugeCoefficients
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.BigOperators.Fin

/-! NEW SOURCE-ONLY, UNCOMPILED. Nonzero array extraction retains the original
ODE tuple. It deliberately asserts neither a nonzero last corner nor Fuchs
support: a lower derivative coefficient can have the largest polynomial degree. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem reciprocalSourcePolynomial_nonzero (m d : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : ∃ i, q i ≠ 0) :
    ∃ k : Fin (m+1), reciprocalSourcePolynomial m d q k.val ≠ 0 := by
  let s : Finset (Fin (m+1)) := Finset.univ.filter fun i => q i ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hq
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image s (fun i => i.val) hs
  have hkq : q k ≠ 0 := (Finset.mem_filter.mp hk).2
  have he : reciprocalSourcePolynomial m d q k.val =
      Polynomial.reflect d (q k) * reciprocalGaugeCoefficient k.val k.val := by
    unfold reciprocalSourcePolynomial
    refine Finset.sum_eq_single k ?_ ?_
    · intro i hi hne
      by_cases hiq : q i = 0
      · rw [hiq, Polynomial.reflect_zero, zero_mul]
      · have hik : i.val ≤ k.val :=
          hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiq⟩)
        have hil : i.val < k.val := by
          have hn : i.val ≠ k.val := fun h => hne (Fin.ext h)
          omega
        rw [reciprocalGaugeCoefficient_above i.val k.val hil, mul_zero]
    · intro h
      exact (h (Finset.mem_univ k)).elim
  refine ⟨k, ?_⟩
  rw [he]
  exact mul_ne_zero (reciprocalPolynomial_ne_zero d _ hkq)
    (reciprocalGaugeCoefficient_diagonal_ne_zero k.val)

def reciprocalSourceDegree (m d : ℕ) (q : Fin (m+1) → Polynomial K) : ℕ :=
  Finset.univ.sup fun k : Fin (m+1) => (reciprocalSourcePolynomial m d q k.val).natDegree

theorem reciprocalSourceDegree_bound (m d : ℕ) (q : Fin (m+1) → Polynomial K)
    (k : Fin (m+1)) :
    (reciprocalSourcePolynomial m d q k.val).natDegree ≤ reciprocalSourceDegree m d q :=
  Finset.le_sup (f := fun k : Fin (m+1) =>
    (reciprocalSourcePolynomial m d q k.val).natDegree) (Finset.mem_univ k)

def reciprocalSourceArray (m d : ℕ) (q : Fin (m+1) → Polynomial K)
    (k : Fin (m+1)) (j : Fin (reciprocalSourceDegree m d q + 1)) : K :=
  (reciprocalSourcePolynomial m d q k.val).coeff j.val

theorem reciprocalSourceArray_nonzero (m d : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : ∃ i, q i ≠ 0) :
    ∃ k j, reciprocalSourceArray m d q k j ≠ 0 := by
  obtain ⟨k, hk⟩ := reciprocalSourcePolynomial_nonzero m d q hq
  let j : Fin (reciprocalSourceDegree m d q + 1) :=
    ⟨(reciprocalSourcePolynomial m d q k.val).natDegree,
      Nat.lt_succ_of_le (reciprocalSourceDegree_bound m d q k)⟩
  refine ⟨k, j, ?_⟩
  change (reciprocalSourcePolynomial m d q k.val).coeff
    (reciprocalSourcePolynomial m d q k.val).natDegree ≠ 0
  rw [Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hk

theorem reciprocalSourceArray_polynomial (m d : ℕ)
    (q : Fin (m+1) → Polynomial K) (k : Fin (m+1)) :
    reciprocalSourcePolynomial m d q k.val =
      ∑ j, Polynomial.C (reciprocalSourceArray m d q k j) * Polynomial.X^j.val := by
  change reciprocalSourcePolynomial m d q k.val =
    ∑ j : Fin (reciprocalSourceDegree m d q + 1),
      Polynomial.C ((reciprocalSourcePolynomial m d q k.val).coeff j.val) *
        Polynomial.X ^ j.val
  calc
    reciprocalSourcePolynomial m d q k.val =
        ∑ j ∈ Finset.range (reciprocalSourceDegree m d q + 1),
          Polynomial.C ((reciprocalSourcePolynomial m d q k.val).coeff j) *
            Polynomial.X ^ j := by
      simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        (Polynomial.as_sum_range' (reciprocalSourcePolynomial m d q k.val)
          (reciprocalSourceDegree m d q + 1)
          (Nat.lt_succ_of_le (reciprocalSourceDegree_bound m d q k)))
    _ = ∑ j : Fin (reciprocalSourceDegree m d q + 1),
        Polynomial.C ((reciprocalSourcePolynomial m d q k.val).coeff j.val) *
          Polynomial.X ^ j.val :=
      (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => Polynomial.C ((reciprocalSourcePolynomial m d q k.val).coeff j) *
          Polynomial.X ^ j) (reciprocalSourceDegree m d q + 1)).symm

/-- One explicit common degree and coefficient array reconstruct the SAME
source tuple, and some actual array coefficient is nonzero. No last-corner,
Fuchs-support, rationality, arithmetic, or solution premise is introduced. -/
theorem exists_reciprocalSourceArray (m d : ℕ)
    (q : Fin (m + 1) → Polynomial K) (hq : ∃ i, q i ≠ 0) :
    ∃ ν : ℕ, ∃ A : Fin (m + 1) → Fin (ν + 1) → K,
      (∀ k : Fin (m + 1), reciprocalSourcePolynomial m d q k.val =
        ∑ j : Fin (ν + 1), Polynomial.C (A k j) * Polynomial.X ^ j.val) ∧
      ∃ k j, A k j ≠ 0 := by
  exact ⟨reciprocalSourceDegree m d q, reciprocalSourceArray m d q,
    fun k => reciprocalSourceArray_polynomial m d q k,
    reciprocalSourceArray_nonzero m d q hq⟩

end StrictEUnit
end
