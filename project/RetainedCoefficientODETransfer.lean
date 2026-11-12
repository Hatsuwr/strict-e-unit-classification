import RetainedCoefficientAnalyticRealization
import Stage14ActualAnalyticODETransfer
import TwistedScalarJetElimination

noncomputable section
namespace StrictEUnit

/-- An actual coefficient's Laurent ODE transfers to its exact entire sum.
The support/embedding equality is explicit: negative Laurent terms may not be dropped. -/
theorem logAmplitudeFactorial_actual_ODE
    (p : Polynomial (LaurentSeries AlgebraicComplex)) (j : ℕ)
    (ha : HasStrictEArithmetic (fun n =>logAmplitudeFactorialCoefficient p j n))
    (hs : HahnSeries.ofPowerSeries ℤ AlgebraicComplex
      (PowerSeries.mk (fun n =>(p.coeff j).coeff (n:ℤ)))=p.coeff j)
    (ho : HasPolynomialScalarDifferentialRelation (k:=AlgebraicComplex)
      stage14_laurentAlgebraDerivation (p.coeff j)) :
    HasAlgebraicPolynomialODE
      (stage41_strictSeriesFunction (fun n =>logAmplitudeFactorialCoefficient p j n)) := by
  apply (stage14_actualODE_iff_laurentODE (algebraicClosure ℚ ℂ).toSubfield
    (stage41_strictSeriesRealization _ ha)).mpr
  rw [stage14_subfieldEntireLaurentAlgHom_apply,
    (logAmplitudeFactorial_actual_realization p j ha).2.2]
  convert ho using 1

end StrictEUnit
end
