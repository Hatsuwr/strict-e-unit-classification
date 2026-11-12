import IntegerClassSharedNormalization
import LaurentLogOperatorBridge

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A genuine polynomial in the actual twisted Euler operator on the
literal polynomial-log Laurent ring. No formal exponent is adjoined. -/
def literalLogPolynomialFilter (rho : K) (P : Polynomial K)
    (f : Polynomial (LaurentSeries K)) : Polynomial (LaurentSeries K) :=
  ∑ i ∈ P.support,P.coeff i • (twistedLogPolynomialEuler rho)^[i] f

/-- Exact extraction at EVERY integer Laurent coefficient, retaining the
whole log polynomial, not just its constant log term. -/
theorem literalLogPolynomialFilter_coefficient (rho : K) (P : Polynomial K)
    (f : Polynomial (LaurentSeries K)) (a : ℤ) :
    (logPolynomialToCoefficientSeries (literalLogPolynomialFilter rho P f)).coeff a=
      shiftedPolynomialDifferentialOperator (rho+(a : K)) P
        ((logPolynomialToCoefficientSeries f).coeff a) := by
  simp only [literalLogPolynomialFilter,map_sum,logPolynomialToCoefficientSeries_smul,
    logPolynomialToCoefficientSeries_twistedEuler_iterate,HahnSeries.coeff_sum,
    HahnSeries.coeff_smul,twistedPolynomialCoefficientEuler_iterate_coeff]
  rw [shiftedPolynomialDifferentialOperator,Polynomial.aeval_endomorphism,Polynomial.sum_def]
  simp only [Module.End.pow_apply]

theorem literalLogPolynomialFilter_double_coefficient (rho : K) (P : Polynomial K)
    (f : Polynomial (LaurentSeries K)) (a : ℤ) (j : ℕ) :
    ((literalLogPolynomialFilter rho P f).coeff j).coeff a=
      (shiftedPolynomialDifferentialOperator (rho+(a : K)) P
        ((logPolynomialToCoefficientSeries f).coeff a)).coeff j := by
  rw [← logPolynomialToCoefficientSeries_double_coeff,literalLogPolynomialFilter_coefficient]

/-- Checked coefficient normalization in the actual Laurent/log ring. The
filtered coefficient arithmetic is an explicit premise here; it is NOT
silently obtained from source-connection arithmetic or asserted for actual
Fourier solutions. The common denominator precedes every f and target a. -/
theorem literal_integerClass_filter_shared_extraction (q d W : ℕ) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤B^(N+1) ∧
      ∀ (rho : K) (s : Fin q → ℤ),(∀ i,(s i).natAbs≤W) →
        ∀ a : ℤ,a.natAbs≤N+W → ∀ ms : Fin q → ℕ,(∀ i,ms i≤N) →
          (integerClassFallingComposite rho s ms).eval (rho+(a : K))≠0 →
          ∀ (Z : K) (f : Polynomial (LaurentSeries K)),
            ((logPolynomialToCoefficientSeries f).coeff a).natDegree≤d →
            (∀ j,IsIntegral ℤ (Z*((literalLogPolynomialFilter rho
              (integerClassFallingComposite rho s ms) f).coeff j).coeff a)) →
            ∀ j,IsIntegral ℤ ((e : K)*Z*(f.coeff j).coeff a) := by
  obtain ⟨B,hB,hden⟩ := integerClassFallingComposite_shared_normalization (K:=K) q d W
  refine ⟨B,hB,?_⟩
  intro N
  obtain ⟨e,he,heb,hei⟩ := hden N
  refine ⟨e,he,heb,?_⟩
  intro rho s hs a ha ms hm hpivot Z f hf hforced j
  rw [← logPolynomialToCoefficientSeries_double_coeff]
  apply hei rho s hs a ha ms hm hpivot Z ((logPolynomialToCoefficientSeries f).coeff a) hf
  intro k
  simpa only [literalLogPolynomialFilter_double_coefficient] using hforced k

end StrictEUnit
end
