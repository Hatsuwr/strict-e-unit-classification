import FourierFrobeniusCoefficientField

/-! The SAME Fourier Euler operator has triangular support: z-degree plus
Euler degree never exceeds nu. This is the finite-width structure needed
before factorial-normalized analytic estimates. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem sameFourierLift_coeff_eq_zero_of_triangle
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (n k : ℕ) (h : ν < n+k) :
    PowerSeries.coeff K n ((stage61_fourierLift A hf).coeff k) = 0 := by
  have he := congrArg (fun s : LaurentSeries K => s.coeff (n : ℤ))
    (stage59_regularLift_map_coeff (stage61_fourierEulerSymbol A)
      (stage61_fourierEulerSymbol_regular A hf) k)
  change (((stage61_fourierLift A hf).coeff k : PowerSeries K) : LaurentSeries K).coeff
    (n : ℤ) = _ at he
  rw [LaurentSeries.coeff_coe_powerSeries] at he
  rw [he,stage61_fourierEulerSymbol_coeff]
  simp only [HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hnj : (n : ℤ) = stage57_exponent i j
  · have hkj : j.1 < k := by
      unfold stage57_exponent at hnj
      have hi' := i.isLt
      omega
    have hzero : (stage61_shiftedDesc (K := K) i.1 j.1).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [stage61_shiftedDesc_natDegree])
    rw [hzero,mul_zero,map_zero,HahnSeries.coeff_zero]
  · exact HahnSeries.coeff_single_of_ne hnj

theorem sameFourierEulerCoefficientSymbols_coeff_eq_zero_of_triangle
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (n k : ℕ) (h : ν < n+k) : (sameFourierEulerCoefficientSymbols A hf n).coeff k = 0 := by
  unfold sameFourierEulerCoefficientSymbols scalarEulerCoefficientSymbol
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_monomial]
  split_ifs with hik
  · subst k
    exact sameFourierLift_coeff_eq_zero_of_triangle A hf n i.1 h
  · rfl

theorem sameFourierEulerCoefficientSymbols_eq_zero_above_order
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (n : ℕ) (hn : ν < n) : sameFourierEulerCoefficientSymbols A hf n = 0 := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_zero]
  exact sameFourierEulerCoefficientSymbols_coeff_eq_zero_of_triangle A hf n k (by omega)

theorem sameFourierEulerCoefficientSymbols_natDegree_le
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (n : ℕ) : (sameFourierEulerCoefficientSymbols A hf n).natDegree ≤ ν-n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact sameFourierEulerCoefficientSymbols_coeff_eq_zero_of_triangle A hf n k (by omega)

/-- The full coefficient equation can use only the last nu+1 coefficient
polynomials. This is exact, including the initial boundary indices. -/
theorem sameFourier_polynomialLogEulerCoefficient_finite_window
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (rho : K) (u : ℕ → Polynomial K) (n : ℕ) :
    polynomialLogEulerCoefficient (sameFourierEulerCoefficientSymbols A hf) rho u n =
      ∑ s : Fin (n+1),if n-s.1 ≤ ν then
        shiftedPolynomialDifferentialOperator (rho+(s.1 : K))
          (sameFourierEulerCoefficientSymbols A hf (n-s.1)) (u s.1) else 0 := by
  unfold polynomialLogEulerCoefficient
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : n-s.1 ≤ ν
  · rw [if_pos h]
  · rw [if_neg h,sameFourierEulerCoefficientSymbols_eq_zero_above_order A hf _
      (Nat.lt_of_not_ge h)]
    simp only [shiftedPolynomialDifferentialOperator,map_zero,LinearMap.zero_apply]

end StrictEUnit
end

#print axioms StrictEUnit.sameFourierLift_coeff_eq_zero_of_triangle
#print axioms StrictEUnit.sameFourierEulerCoefficientSymbols_coeff_eq_zero_of_triangle
#print axioms StrictEUnit.sameFourierEulerCoefficientSymbols_eq_zero_above_order
#print axioms StrictEUnit.sameFourierEulerCoefficientSymbols_natDegree_le
#print axioms StrictEUnit.sameFourier_polynomialLogEulerCoefficient_finite_window
