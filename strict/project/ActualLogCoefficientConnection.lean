import TwistedLogOrdinaryCoefficientBridge
import LaurentOrdinaryDerivation

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The exact coupled ordinary-derivative equation for a log coefficient.
The next logarithmic coefficient is retained, not incorrectly projected away. -/
theorem actualTwistedLogOrdinary_log_coefficient (rho : K)
    (p : Polynomial (LaurentSeries K)) (j : ℕ) :
    (actualTwistedLogOrdinary rho p).coeff j=
      laurentOrdinaryDerivation (p.coeff j)+HahnSeries.single (-1:ℤ) rho*p.coeff j+
      HahnSeries.single (-1:ℤ) ((j+1:ℕ):K)*p.coeff (j+1) := by
  apply HahnSeries.ext
  funext n
  rw [actualTwistedLogOrdinary_shiftedEuler,frobeniusIntegerShift_coeff,
    twistedLogPolynomialEuler_double_coeff]
  simp only [HahnSeries.coeff_add,laurentOrdinaryDerivation_coeff]
  have hs (a : K) (f : LaurentSeries K) :
      (HahnSeries.single (-1:ℤ) a*f).coeff n=a*f.coeff (n+1) := by
    simpa using (HahnSeries.coeff_single_mul_add (r:=a) (x:=f) (a:=n+1) (b:=(-1:ℤ)))
  rw [hs,hs,show n-(-1)=n+1 by omega]
  push_cast
  ring
end StrictEUnit
end
