import GeneralizedLogOrdinaryJet
import CoefficientEulerLeibniz
import ReciprocalGaugeLaurent

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem twistedLogCoefficientEuler_formula (rho : K) (s : LaurentSeries (Polynomial K)) :
    twistedLogCoefficientEuler rho s=polynomialCoefficientEuler 1 s+rho • s := by
  apply HahnSeries.ext
  funext n
  exact (twistedPolynomialCoefficientEuler_coeff rho s n).symm

theorem generalizedLogOrdinaryDerivative_add (rho : K) (f g : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho (f+g)=
      generalizedLogOrdinaryDerivative rho f+generalizedLogOrdinaryDerivative rho g := by
  simp only [generalizedLogOrdinaryDerivative,twistedLogCoefficientEuler_formula,smul_add]
  rw [show polynomialCoefficientEuler 1 (f+g)=polynomialCoefficientEuler 1 f+polynomialCoefficientEuler 1 g from
    coefficientEulerAdd.map_add f g]
  ring

def generalizedLogOrdinaryDerivativeAdd (rho : K) :
    LaurentSeries (Polynomial K) →+ LaurentSeries (Polynomial K) where
  toFun := generalizedLogOrdinaryDerivative rho
  map_zero' := by
    simp [generalizedLogOrdinaryDerivative,twistedLogCoefficientEuler_formula,
      show polynomialCoefficientEuler (1:K) 0=0 from coefficientEulerAdd.map_zero]
  map_add' := generalizedLogOrdinaryDerivative_add rho

/-- Twisting affects the solution factor once, not the coefficient factor. -/
theorem generalizedLogOrdinaryDerivative_mul (rho : K) (f g : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho (f*g)=
      generalizedLogOrdinaryDerivative 0 f*g+f*generalizedLogOrdinaryDerivative rho g := by
  simp only [generalizedLogOrdinaryDerivative,twistedLogCoefficientEuler_formula,
    coefficientLaurentEuler_mul,zero_smul,add_zero,laurentCoefficient_smul_eq_mul,
    map_zero,mul_zero]
  ring

theorem logMonomial_one_mul_coeff (k n : ℤ) (s : LaurentSeries (Polynomial K)) :
    (HahnSeries.single k (1:Polynomial K)*s).coeff n=s.coeff (n-k) := by
  have he : n=(n-k)+k := by omega
  conv_lhs => rw [he]
  rw [HahnSeries.coeff_single_mul_add,one_mul]

theorem generalizedLogOrdinaryDerivative_logfree (a : LaurentSeries K) :
    generalizedLogOrdinaryDerivative 0 (logLaurentCoefficientMap a)=
      logLaurentCoefficientMap (laurentOrdinaryDerivation a) := by
  apply HahnSeries.ext
  funext n
  simp only [generalizedLogOrdinaryDerivative,logMonomial_one_mul_coeff,
    twistedLogCoefficientEuler,logLaurentCoefficientMap_coeff,shiftedPolynomialDerivative_apply,
    Polynomial.derivative_C,zero_add,zero_add,Polynomial.smul_eq_C_mul,← map_mul,
    laurentOrdinaryDerivation_coeff]
  norm_num

theorem generalizedLogOrdinaryDerivative_logfree_mul (rho : K) (a : LaurentSeries K)
    (s : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho (logLaurentCoefficientMap a*s)=
      logLaurentCoefficientMap (laurentOrdinaryDerivation a)*s+
        logLaurentCoefficientMap a*generalizedLogOrdinaryDerivative rho s := by
  rw [generalizedLogOrdinaryDerivative_mul,generalizedLogOrdinaryDerivative_logfree]

end StrictEUnit
end
