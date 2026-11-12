import SignedLaplaceFirstNuBoundary
import Mathlib.RingTheory.Polynomial.Pochhammer

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem signedLaplace_z_iterate_coeff (y : LaurentSeries K) (j : ℕ) (m : ℤ) :
    ((fun x : LaurentSeries K => HahnSeries.single (-1:ℤ) (1:K) * x)^[j] y).coeff m =
      y.coeff (m+(j:ℤ)) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', signedLaplace_single_coeff]
    simp only [one_mul]
    rw [ih]
    congr 1
    omega

theorem signedLaplace_Dz_iterate_coeff (y : LaurentSeries K) (i : ℕ) (m : ℤ) :
    ((fun x : LaurentSeries K => HahnSeries.single (2:ℤ) (-1:K) *
      laurentOrdinaryDerivation x)^[i] y).coeff m =
      (-1:K)^i * (descPochhammer K i).eval (((m-1:ℤ):K)) *
        y.coeff (m-(i:ℤ)) := by
  induction i generalizing m with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', signedLaplace_single_coeff,
      laurentOrdinaryDerivation_coeff]
    rw [show m-2+1=m-1 by omega, ih, descPochhammer_succ_left]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_one, pow_succ, Int.cast_sub, Int.cast_one]
    rw [show m-1-(i:ℤ)=m-((i+1:ℕ):ℤ) by omega]
    ring

theorem signedLaplaceSourceAction_coeff {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) (m : ℤ) :
    (signedLaplaceSourceAction A y).coeff m =
      ∑ i, ∑ j, A i j * (-1:K)^i.val *
        (descPochhammer K i.val).eval (((m+(j.val:ℤ)-1:ℤ):K)) *
          y.coeff (m+(j.val:ℤ)-(i.val:ℤ)) := by
  simp only [signedLaplaceSourceAction, HahnSeries.coeff_sum,
    signedLaplace_single_coeff, sub_zero, signedLaplace_z_iterate_coeff,
    signedLaplace_Dz_iterate_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem signedOrdinarySource_coeff (a : ℕ → K) (m : ℤ) :
    (signedOrdinarySource a).coeff m =
      if 1 ≤ m then (-1:K)^((m-1).toNat) * a ((m-1).toNat) else 0 := by
  by_cases hm : 1 ≤ m
  · rw [if_pos hm, signedOrdinarySource, signedLaplace_single_coeff, one_mul]
    have he : (((m-1).toNat:ℕ):ℤ) = m-1 := Int.toNat_of_nonneg (by omega)
    rw [← he, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
    simp only [Int.toNat_natCast]
  · rw [if_neg hm]
    exact signedOrdinarySource_coeff_lt_one a m (by omega)

/-- Exact signed nonpositive coefficients. Every natural subtraction is inside
its genuine active guard; the factorial multiplier occurs without division. -/
theorem signedLaplaceSourceAction_canonical_neg_coeff {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) (k : ℕ) :
    (signedLaplaceSourceAction A (signedOrdinarySource a)).coeff (-(k:ℤ)) =
      ∑ i, ∑ j, if i.val+k < j.val then
        A i j * (-1:K)^(j.val-k-1) *
          (((j.val-k-1).descFactorial i.val):K) * a (j.val-i.val-k-1)
        else 0 := by
  rw [signedLaplaceSourceAction_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [signedOrdinarySource_coeff]
  by_cases h : i.val+k < j.val
  · have hc : 1 ≤ -(k:ℤ)+(j.val:ℤ)-(i.val:ℤ) := by omega
    rw [if_pos hc, if_pos h]
    have hN : (-(k:ℤ)+(j.val:ℤ)-(i.val:ℤ)-1).toNat = j.val-i.val-k-1 := by omega
    have hP : -(k:ℤ)+(j.val:ℤ)-1 = ((j.val-k-1:ℕ):ℤ) := by omega
    rw [hN, hP, Int.cast_natCast, descPochhammer_eval_eq_descFactorial]
    have hs : (-1:K)^i.val * (-1:K)^(j.val-i.val-k-1) = (-1:K)^(j.val-k-1) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _ = A i j * ((-1:K)^i.val * (-1:K)^(j.val-i.val-k-1)) *
          (((j.val-k-1).descFactorial i.val):K) * a (j.val-i.val-k-1) := by ring
      _ = _ := by rw [hs]
  · have hc : ¬ 1 ≤ -(k:ℤ)+(j.val:ℤ)-(i.val:ℤ) := by omega
    rw [if_neg hc, if_neg h, mul_zero]

/-- The order cutoff never loses any nonpositive coefficient of a Laurent
series, even before any Fourier-vanishing hypothesis. -/
theorem signedLaplaceKernelPolynomial_coeff_all (S : LaurentSeries K) (k : ℕ) :
    (signedLaplaceKernelPolynomial S).coeff k = S.coeff (-(k:ℤ)) := by
  rw [signedLaplaceKernelPolynomial_coeff]
  by_cases hk : k ≤ (-S.order).toNat
  · rw [if_pos hk]
  · rw [if_neg hk]
    symm
    have hbound : -((((-S.order).toNat:ℕ):ℤ)) ≤ S.order := by
      by_cases ho : S.order ≤ 0
      · have hb : (((-S.order).toNat:ℕ):ℤ) = -S.order := Int.toNat_of_nonneg (by omega)
        omega
      · have hb : (0:ℤ) ≤ (((-S.order).toNat:ℕ):ℤ) := Nat.cast_nonneg _
        omega
    apply HahnSeries.coeff_eq_zero_of_lt_order
    omega

theorem signedLaplaceBoundaryPolynomial_eq_firstNu {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) :
    signedLaplaceBoundaryPolynomial A (signedOrdinarySource a) =
      signedLaplaceFirstNuBoundary A a := by
  ext k
  rw [signedLaplaceBoundaryPolynomial, signedLaplaceKernelPolynomial_coeff_all,
    signedLaplaceFirstNuBoundary, laurentFirstNuBoundary_coeff]
  by_cases hk : k < ν
  · rw [if_pos hk]
  · rw [if_neg hk]
    exact signedLaplaceSourceAction_canonical_lower_support A a (-(k:ℤ)) (by omega)

theorem signedLaplaceFirstNuBoundary_coeff_formula {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) (k : ℕ) :
    (signedLaplaceFirstNuBoundary A a).coeff k =
      ∑ i, ∑ j, if i.val+k < j.val then
        A i j * (-1:K)^(j.val-k-1) *
          (((j.val-k-1).descFactorial i.val):K) * a (j.val-i.val-k-1)
        else 0 := by
  rw [← signedLaplaceBoundaryPolynomial_eq_firstNu, signedLaplaceBoundaryPolynomial,
    signedLaplaceKernelPolynomial_coeff_all, signedLaplaceSourceAction_canonical_neg_coeff]

/-- Changing the tail preserves the boundary polynomial, not the Fourier
annihilation equation itself. Only the first nu coefficients are read. -/
theorem signedLaplaceFirstNuBoundary_prefix_congr {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a b : ℕ → K)
    (hab : ∀ n, n < ν → a n = b n) :
    signedLaplaceFirstNuBoundary A a = signedLaplaceFirstNuBoundary A b := by
  ext k
  rw [signedLaplaceFirstNuBoundary_coeff_formula, signedLaplaceFirstNuBoundary_coeff_formula]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i.val+k < j.val
  · rw [if_pos h, if_pos h, hab _ (by have hjν := j.isLt; omega)]
  · rw [if_neg h, if_neg h]

end StrictEUnit
end
