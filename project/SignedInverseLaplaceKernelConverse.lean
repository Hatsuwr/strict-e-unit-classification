import SignedInverseLaplaceKernel

/-!
# The signed inverse-Laplace kernel consists exactly of polynomials in z

The polynomial witness is explicit: reverse the nonpositive coefficient
indices and truncate at B+1, where B=(-order y).toNat. The Laurent lower
support bound makes every omitted negative coefficient zero. No external
support bound or polynomial-representation hypothesis is introduced.
-/
noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A monomial in z=w⁻¹ is the corresponding nonpositive Laurent monomial. -/
theorem signedLaplacePolynomialInZ_monomial (n : ℕ) (c : K) :
    signedLaplacePolynomialInZ (Polynomial.monomial n c) =
      HahnSeries.single (-(n : ℤ)) c := by
  rw [signedLaplacePolynomialInZ, Polynomial.eval₂_monomial, HahnSeries.C_apply,
    HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp only [one_pow, mul_one, zero_add, nsmul_eq_mul, mul_neg]

/-- Exact coefficients at every integer exponent, including exponent zero. -/
theorem signedLaplacePolynomialInZ_coeff (P : Polynomial K) (m : ℤ) :
    (signedLaplacePolynomialInZ P).coeff m =
      if m ≤ 0 then P.coeff (-m).toNat else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      change ((P + Q).eval₂ (HahnSeries.C : K →+* LaurentSeries K)
        (HahnSeries.single (-1 : ℤ) (1 : K))).coeff m = _
      rw [Polynomial.eval₂_add, HahnSeries.coeff_add]
      change (signedLaplacePolynomialInZ P).coeff m +
        (signedLaplacePolynomialInZ Q).coeff m = _
      rw [hP, hQ]
      split_ifs <;> simp only [Polynomial.coeff_add, add_zero]
  | monomial n c =>
      rw [signedLaplacePolynomialInZ_monomial, HahnSeries.coeff_single]
      by_cases hm : m ≤ 0
      · rw [if_pos hm, Polynomial.coeff_monomial]
        have hk : (((-m).toNat : ℕ) : ℤ) = -m :=
          Int.toNat_of_nonneg (by omega)
        have he : m = -(n : ℤ) ↔ n = (-m).toNat := by omega
        simp only [he]
      · have he : m ≠ -(n : ℤ) := by omega
        rw [if_neg hm, if_neg he]

/-- The explicit finite polynomial candidate, defined for every Laurent series. -/
def signedLaplaceKernelPolynomial (y : LaurentSeries K) : Polynomial K :=
  PowerSeries.trunc ((-y.order).toNat + 1)
    (PowerSeries.mk (fun n => y.coeff (-(n : ℤ))))

/-- The candidate retains precisely the reversed coefficients up to B. -/
theorem signedLaplaceKernelPolynomial_coeff (y : LaurentSeries K) (n : ℕ) :
    (signedLaplaceKernelPolynomial y).coeff n =
      if n ≤ (-y.order).toNat then y.coeff (-(n : ℤ)) else 0 := by
  simp only [signedLaplaceKernelPolynomial, PowerSeries.coeff_trunc,
    PowerSeries.coeff_mk, Nat.lt_succ_iff]

/-- A concrete degree bound, also valid when the series or polynomial is zero. -/
theorem signedLaplaceKernelPolynomial_natDegree_le (y : LaurentSeries K) :
    (signedLaplaceKernelPolynomial y).natDegree ≤ (-y.order).toNat := by
  exact Nat.lt_succ_iff.mp
    (PowerSeries.natDegree_trunc_lt
      (PowerSeries.mk (fun n => y.coeff (-(n : ℤ)))) (-y.order).toNat)

/-- The actual Laurent lower bound and the exact positive-coefficient kernel
condition prove reconstruction by the explicit finite candidate. -/
theorem signedInverseLaplace_kernel_reconstruct (y : LaurentSeries K)
    (hy : signedInverseLaplace y = 0) :
    y = signedLaplacePolynomialInZ (signedLaplaceKernelPolynomial y) := by
  have hpos := (signedInverseLaplace_eq_zero_iff y).mp hy
  have hbound : -((((-y.order).toNat : ℕ) : ℤ)) ≤ y.order := by
    by_cases ho : y.order ≤ 0
    · have hb : (((-y.order).toNat : ℕ) : ℤ) = -y.order :=
        Int.toNat_of_nonneg (by omega)
      omega
    · have hb : (0 : ℤ) ≤ ((-y.order).toNat : ℕ) := Nat.cast_nonneg _
      omega
  ext m
  rw [signedLaplacePolynomialInZ_coeff]
  by_cases hm : m ≤ 0
  · rw [if_pos hm, signedLaplaceKernelPolynomial_coeff]
    have hk : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    by_cases hkm : (-m).toNat ≤ (-y.order).toNat
    · rw [if_pos hkm, hk, neg_neg]
    · rw [if_neg hkm]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      omega
  · rw [if_neg hm]
    have hm1 : 0 ≤ m - 1 := by omega
    have hn : (((m - 1).toNat : ℕ) : ℤ) + 1 = m := by
      rw [Int.toNat_of_nonneg hm1]
      omega
    rw [← hn]
    exact hpos ((m - 1).toNat)

/-- Exact kernel classification with an actual polynomial in z=w⁻¹.
The forward direction constructs the polynomial, rather than assuming one. -/
theorem signedInverseLaplace_eq_zero_iff_exists_polynomialInZ (y : LaurentSeries K) :
    signedInverseLaplace y = 0 ↔
      ∃ P : Polynomial K, y = signedLaplacePolynomialInZ P := by
  constructor
  · intro hy
    exact ⟨signedLaplaceKernelPolynomial y, signedInverseLaplace_kernel_reconstruct y hy⟩
  · rintro ⟨P, rfl⟩
    exact signedInverseLaplace_polynomialInZ P

end StrictEUnit
end
