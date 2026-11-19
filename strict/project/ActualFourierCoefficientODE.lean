import ActualFourierRationalTuple
import RetainedCoefficientActualODE

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Scalar ordinary ODEs for every log coefficient of an actual Stage53
solution, from its literal nonzero corner. Includes order zero. -/
theorem actualTwistedStage53_coefficient_polynomialODE {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →K)
    (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (rho : K) (p : Polynomial (LaurentSeries K))
    (h : actualTwistedStage53Action rho A p=0) :
    ∀ j,HasPolynomialScalarDifferentialRelation (k:=K)
      stage14_laurentAlgebraDerivation (p.coeff j) := by
  let q (i : Fin (nu+1)) : RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K) (stage53_fourierCoeff A i)
  have hq : q (Fin.last nu)≠0 := by
    exact RatFunc.algebraMap_ne_zero (stage53_fourierCoeff_last_ne_zero A hc)
  have he : (∑ i,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q i))*
      (actualTwistedLogOrdinary rho)^[i.val] p)=0 := by
    simpa only [actualTwistedStage53Action,sourceCoordinate_polynomial_rational,q] using h
  cases nu with
  | succ n => exact rationalTwistedEquation_coefficient_polynomialODE rho p n q hq he
  | zero =>
    change (∑ i : Fin 1,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q i))*
      (actualTwistedLogOrdinary rho)^[i.val] p)=0 at he
    have hp : p=0 := by
      have he' : Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q 0))*p=0 := by
        simpa only [Fin.sum_univ_one,Fin.val_zero,Function.iterate_zero_apply] using he
      apply (mul_eq_zero.mp he').resolve_left
      intro hz
      apply hq
      apply (algebraMap (RatFunc K) (LaurentSeries K)).injective
      apply Polynomial.C_injective
      simpa only [map_zero] using hz
    subst p
    intro j
    refine ⟨0,fun _ =>1,⟨0,one_ne_zero⟩,?_⟩
    simp

theorem sameFourierTwistedAmplitude_coefficient_polynomialODE {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) :
    ∀ j,HasPolynomialScalarDifferentialRelation (k:=K) stage14_laurentAlgebraDerivation
      ((sameFourierTwistedAmplitude A hf i).coeff j) :=
  actualTwistedStage53_coefficient_polynomialODE A hc _ _
    (sameFourierTwistedAmplitude_stage53 A hf hc i)
end StrictEUnit
end
