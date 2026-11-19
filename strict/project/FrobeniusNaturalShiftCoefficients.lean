import FrobeniusRepresentedCoefficientDetection
import FrobeniusIntegerShiftEquation

/-!
# The exact nonnegative resonance family as coefficient solutions

The family is indexed by actual natural resonances and their root
multiplicities. Each member is the existing Frobenius recurrence, shifted by
the corresponding nonnegative integer. Representation and the literal equation
are proved, rather than supplied as family hypotheses.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

def naturalCoefficientShift (s : ℕ) (u : ℕ → Polynomial K) (m : ℕ) : Polynomial K :=
  if s ≤ m then u (m-s) else 0

theorem powerSeries_mk_naturalCoefficientShift (s : ℕ) (u : ℕ → Polynomial K) :
    PowerSeries.mk (naturalCoefficientShift s u) =
      (PowerSeries.X : PowerSeries (Polynomial K))^s * PowerSeries.mk u := by
  apply PowerSeries.ext
  intro m
  simp only [PowerSeries.coeff_mk,PowerSeries.coeff_X_pow_mul',naturalCoefficientShift]

theorem logPolynomialToCoefficientSeries_naturalShift
    (s : ℕ) (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K))) :
    logPolynomialToCoefficientSeries (frobeniusIntegerShift (s : ℤ) p) =
      ((PowerSeries.mk (naturalCoefficientShift s u) : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K)) := by
  have hm : logLaurentCoefficientMap (HahnSeries.single (s : ℤ) (1 : K)) =
      (HahnSeries.single (s : ℤ) (1 : Polynomial K) : LaurentSeries (Polynomial K)) := by
    apply HahnSeries.ext
    funext n
    simp only [logLaurentCoefficientMap_coeff,HahnSeries.coeff_single]
    split_ifs <;> simp
  rw [frobeniusIntegerShift,map_mul,logPolynomialToCoefficientSeries_C,hm,hp,
    powerSeries_mk_naturalCoefficientShift,PowerSeries.coe_mul,HahnSeries.ofPowerSeries_X_pow]

variable [CharZero K]

/-- Actual shifted coefficients from the existing recurrence and monomial seed. -/
def naturalResonanceFrobeniusCoefficients (B : ℕ → Polynomial K) (ξ : K)
    (i : polynomialLogResonanceCoordinateIndex ξ (B 0)) : ℕ → Polynomial K :=
  naturalCoefficientShift i.1.1
    (polynomialLogFrobeniusCoefficient B (ξ + (i.1.1 : K)) (Polynomial.X ^ i.2.1))

/-- The corresponding literal polynomial-log amplitude uses only an integer shift. -/
def naturalResonanceFrobeniusAmplitude (B : ℕ → Polynomial K) (ξ : K)
    (i : polynomialLogResonanceCoordinateIndex ξ (B 0)) : Polynomial (LaurentSeries K) :=
  frobeniusIntegerShift (i.1.1 : ℤ)
    (polynomialLogFrobeniusAmplitude B (ξ + (i.1.1 : K)) (Polynomial.X ^ i.2.1))

theorem naturalResonanceFrobeniusAmplitude_representation
    (B : ℕ → Polynomial K) (ξ : K)
    (i : polynomialLogResonanceCoordinateIndex ξ (B 0)) :
    logPolynomialToCoefficientSeries (naturalResonanceFrobeniusAmplitude B ξ i) =
      ((PowerSeries.mk (naturalResonanceFrobeniusCoefficients B ξ i) :
        PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) := by
  apply logPolynomialToCoefficientSeries_naturalShift
  exact logPolynomialToCoefficientSeries_transpose_powerSeries_mk _ _
    (polynomialLogFrobeniusCoefficient_coeff_eq_zero _ _ _)

/-- Every indexed member satisfies the SAME coefficient equation. No
nonresonance, independence or completeness hypothesis is used. -/
theorem naturalResonanceFrobeniusCoefficients_solution
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogResonanceCoordinateIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    ∀ m,polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ
      (naturalResonanceFrobeniusCoefficients
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ i) m = 0 := by
  let B := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))
  apply (scalarTwistedLogOperator_eq_zero_iff_coefficients r b ξ
    (naturalResonanceFrobeniusAmplitude B ξ i) _
    (naturalResonanceFrobeniusAmplitude_representation B ξ i)).mp
  unfold naturalResonanceFrobeniusAmplitude
  rw [frobeniusIntegerShift_scalarTwistedLogOperator]
  have he := polynomialLogFrobeniusAmplitude_ring_equation r b
    (ξ + (i.1.1 : K)) (Polynomial.X ^ i.2.1) hP
    (shiftedPolynomialDifferentialOperator_X_pow_eq_zero (B 0)
      (ξ + (i.1.1 : K)) hP i.2)
  change scalarTwistedLogOperator r b (ξ + (i.1.1 : K))
    (polynomialLogFrobeniusAmplitude B (ξ + (i.1.1 : K)) (Polynomial.X ^ i.2.1)) = 0 at he
  simpa only [Int.cast_natCast,he,frobeniusIntegerShift,mul_zero]

end StrictEUnit
end

#print axioms StrictEUnit.powerSeries_mk_naturalCoefficientShift
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_naturalShift
#print axioms StrictEUnit.naturalResonanceFrobeniusAmplitude_representation
#print axioms StrictEUnit.naturalResonanceFrobeniusCoefficients_solution
