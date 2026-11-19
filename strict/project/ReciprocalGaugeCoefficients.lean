import SignedInverseLaplace
import Mathlib.Algebra.Polynomial.Reverse

/-! NEW SOURCE-ONLY, UNCOMPILED. Polynomial coefficient core of reciprocal
variable/gauge conversion. It does not yet assert the Laurent action identity,
source-annihilator existence, Fuchs support, or arithmetic local solutions. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Coefficients of (-z² D_z)^i (z y), normal ordered in D_z.
The zero predecessor at k=0 is explicit. -/
def reciprocalGaugeCoefficient : ℕ → ℕ → Polynomial K
  | 0, k => if k = 0 then Polynomial.X else 0
  | i+1, k => -(Polynomial.X^2) * Polynomial.derivative (reciprocalGaugeCoefficient i k) -
      Polynomial.X^2 * (if k = 0 then 0 else reciprocalGaugeCoefficient i (k-1))

theorem reciprocalGaugeCoefficient_above (i k : ℕ) (h : i < k) :
    reciprocalGaugeCoefficient (K := K) i k = 0 := by
  induction i generalizing k with
  | zero => simp only [reciprocalGaugeCoefficient, if_neg (by omega : k ≠ 0)]
  | succ i ih =>
    have hk : k ≠ 0 := by omega
    have h1 := ih k (by omega)
    have h2 := ih (k-1) (by omega)
    simp only [reciprocalGaugeCoefficient, h1, h2, if_neg hk,
      map_zero, mul_zero, sub_self]

theorem reciprocalGaugeCoefficient_diagonal (i : ℕ) :
    reciprocalGaugeCoefficient (K := K) i i =
      Polynomial.C ((-1 : K)^i) * Polynomial.X^(2*i+1) := by
  induction i with
  | zero => simp only [reciprocalGaugeCoefficient, if_pos rfl, if_true, pow_zero,
      map_one, one_mul, mul_zero, zero_add, pow_one]
  | succ i ih =>
    rw [reciprocalGaugeCoefficient,
      reciprocalGaugeCoefficient_above i (i+1) (by omega), map_zero,
      mul_zero, if_neg (by omega : i+1 ≠ 0), Nat.add_sub_cancel, ih]
    rw [show 2*(i+1)+1 = 2+(2*i+1) by omega, pow_add, pow_succ (-1 : K) i,
      map_mul, map_neg, map_one]
    ring

theorem reciprocalGaugeCoefficient_diagonal_ne_zero (i : ℕ) :
    reciprocalGaugeCoefficient (K := K) i i ≠ 0 := by
  rw [reciprocalGaugeCoefficient_diagonal]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
    (pow_ne_zero _ Polynomial.X_ne_zero)

/-- One common reciprocal denominator suffices for the entire input tuple. -/
def reciprocalCommonDegree (m : ℕ) (q : Fin (m+1) → Polynomial K) : ℕ :=
  Finset.univ.sup fun i => (q i).natDegree

theorem reciprocalCommonDegree_bound (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (i : Fin (m+1)) : (q i).natDegree ≤ reciprocalCommonDegree m q :=
  Finset.le_sup (f := fun i : Fin (m+1) => (q i).natDegree) (Finset.mem_univ i)

/-- Fixed-degree reversal is nonzero even for the zero-degree boundary case. -/
theorem reciprocalPolynomial_ne_zero (d : ℕ) (q : Polynomial K) (hq : q ≠ 0) :
    Polynomial.reflect d q ≠ 0 := by
  exact fun h => hq (Polynomial.reflect_eq_zero_iff.mp h)

/-- Explicit source polynomial coefficients, indexed by D_z order.
The subsequent finite coefficient array uses polynomial power as its second index. -/
def reciprocalSourcePolynomial (m d : ℕ) (q : Fin (m+1) → Polynomial K)
    (k : ℕ) : Polynomial K :=
  ∑ i, Polynomial.reflect d (q i) * reciprocalGaugeCoefficient i.val k

theorem reciprocalSourcePolynomial_top (m d : ℕ)
    (q : Fin (m+1) → Polynomial K) :
    reciprocalSourcePolynomial m d q m =
      Polynomial.reflect d (q (Fin.last m)) *
        (Polynomial.C ((-1 : K)^m) * Polynomial.X^(2*m+1)) := by
  unfold reciprocalSourcePolynomial
  rw [Finset.sum_eq_single (Fin.last m)]
  · exact congrArg (fun P => Polynomial.reflect d (q (Fin.last m)) * P)
      (reciprocalGaugeCoefficient_diagonal m)
  · intro i hi hne
    have him : i.val < m := by
      have hbound := i.isLt
      have hn : i.val ≠ m := fun h => hne (Fin.ext h)
      omega
    rw [reciprocalGaugeCoefficient_above i.val m him, mul_zero]
  · intro h
    exact (h (Finset.mem_univ (Fin.last m))).elim

theorem reciprocalSourcePolynomial_top_ne_zero (m d : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0) :
    reciprocalSourcePolynomial m d q m ≠ 0 := by
  rw [reciprocalSourcePolynomial_top]
  apply mul_ne_zero (reciprocalPolynomial_ne_zero d _ hq)
  rw [← reciprocalGaugeCoefficient_diagonal]
  exact reciprocalGaugeCoefficient_diagonal_ne_zero m

end StrictEUnit
end
