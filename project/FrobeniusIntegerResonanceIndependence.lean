import FrobeniusIntegerResonanceSpace

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The coefficient embedding with the coefficientwise K-module instances. -/
def logPolynomialCoefficientLinear :
    Polynomial (LaurentSeries K) →ₗ[K] LaurentSeries (Polynomial K) where
  toFun := logPolynomialToCoefficientSeries
  map_add' p q := map_add _ p q
  map_smul' c p := by
    apply HahnSeries.ext
    funext n
    apply Polynomial.ext
    intro j
    simp only [logPolynomialToCoefficientSeries_double_coeff,Polynomial.coeff_smul,
      HahnSeries.coeff_smul,RingHom.id_apply]

variable [CharZero K]

theorem polynomialLogIntegerResonanceIndex_pair_injective (ξ : K) (P : Polynomial K) :
    Function.Injective (fun i : polynomialLogIntegerResonanceIndex ξ P => (i.1.1,i.2.1)) := by
  intro i j h
  have h1 : i.1 = j.1 := Subtype.ext (congrArg Prod.fst h)
  cases i with
  | mk i m =>
    cases j with
    | mk j n =>
      dsimp only at h1
      subst j
      have h2 : m = n := Fin.ext (congrArg Prod.snd h)
      subst n
      rfl

theorem integerResonanceFrobeniusAmplitude_linearIndependent (B : ℕ → Polynomial K) (ξ : K) :
    LinearIndependent K (integerResonanceFrobeniusAmplitude B ξ) :=
  polynomialLogFrobeniusAmplitude_integerShift_linearIndependent B _ _ _
    (polynomialLogIntegerResonanceIndex_pair_injective ξ (B 0))

theorem integerResonanceFrobeniusCoefficients_linearIndependent (B : ℕ → Polynomial K) (ξ : K) :
    LinearIndependent K (integerResonanceFrobeniusCoefficients B ξ) := by
  have h := (integerResonanceFrobeniusAmplitude_linearIndependent B ξ).map'
    logPolynomialCoefficientLinear
    (LinearMap.ker_eq_bot.mpr logPolynomialToCoefficientSeries_injective)
  simpa only [Function.comp_def,logPolynomialCoefficientLinear,LinearMap.coe_mk,
    AddHom.coe_mk,integerResonanceFrobeniusAmplitude_representation] using h

theorem integerResonanceFrobeniusCoefficients_solution
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    scalarTwistedCoefficientOperator r b ξ (integerResonanceFrobeniusCoefficients
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ i) = 0 := by
  let B := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))
  rw [← integerResonanceFrobeniusAmplitude_representation,
    ← logPolynomialToCoefficientSeries_scalarTwistedCoefficientOperator]
  have he := polynomialLogFrobeniusAmplitude_ring_equation r b (ξ+(i.1.1 : K))
    (Polynomial.X^i.2.1) hP
    (shiftedPolynomialDifferentialOperator_X_pow_eq_zero (B 0) (ξ+(i.1.1 : K)) hP i.2)
  change scalarTwistedLogOperator r b (ξ+(i.1.1 : K))
    (polynomialLogFrobeniusAmplitude B (ξ+(i.1.1 : K)) (Polynomial.X^i.2.1)) = 0 at he
  change logPolynomialToCoefficientSeries (scalarTwistedLogOperator r b ξ
    (integerResonanceFrobeniusAmplitude B ξ i)) = 0
  rw [integerResonanceFrobeniusAmplitude,frobeniusIntegerShift_scalarTwistedLogOperator,
    he,frobeniusIntegerShift,mul_zero,map_zero]

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogIntegerResonanceIndex_pair_injective
#print axioms StrictEUnit.integerResonanceFrobeniusAmplitude_linearIndependent
#print axioms StrictEUnit.integerResonanceFrobeniusCoefficients_linearIndependent
#print axioms StrictEUnit.integerResonanceFrobeniusCoefficients_solution
