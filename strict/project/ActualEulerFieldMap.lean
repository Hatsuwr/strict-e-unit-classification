import GeneralizedLogLaplaceFieldMap
import ActualFramePreimageArithmetic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

def logCoefficientFieldHom (phi : K →+* L) :
    LaurentSeries (Polynomial K) →+* LaurentSeries (Polynomial L) where
  toFun :=logCoefficientFieldMap phi
  map_zero' :=by apply HahnSeries.ext; funext n; simp [logCoefficientFieldMap]
  map_one' :=HahnSeries.map_one (Polynomial.mapRingHom phi).toMonoidWithZeroHom
  map_add' x y :=HahnSeries.map_add (Polynomial.mapRingHom phi).toAddMonoidHom
  map_mul' x y :=HahnSeries.map_mul (Polynomial.mapRingHom phi).toNonUnitalRingHom

theorem twistedLogCoefficientEuler_eq (rho : K) (u : LaurentSeries (Polynomial K)) :
    twistedLogCoefficientEuler rho u=twistedPolynomialCoefficientEuler rho u := by
  apply HahnSeries.ext
  funext n
  exact (twistedPolynomialCoefficientEuler_coeff rho u n).symm

theorem actualEuler_field_map (phi : K →+* L) (rho : K)
    (u : LaurentSeries (Polynomial K)) :
    logCoefficientFieldHom phi (twistedPolynomialCoefficientEuler rho u)=
      twistedPolynomialCoefficientEuler (phi rho) (logCoefficientFieldHom phi u) := by
  apply HahnSeries.ext
  funext n
  change ((twistedPolynomialCoefficientEuler rho u).coeff n).map phi=_
  rw [twistedPolynomialCoefficientEuler_coeff,shiftedPolynomialDerivative_field_map,
    twistedPolynomialCoefficientEuler_coeff]
  simp only [map_add,map_intCast]
  rfl

theorem actualPowerSeries_log_embedding (f : PowerSeries K) :
    logPolynomialToCoefficientSeries (logPowerSeriesEmbedding f)=
      logLaurentCoefficientMap (HahnSeries.ofPowerSeries ℤ K f) := by
  exact logPolynomialToCoefficientSeries_C _

theorem actualPowerSeries_log_field_map (phi : K →+* L) (f : PowerSeries K) :
    logCoefficientFieldHom phi (logPolynomialToCoefficientSeries (logPowerSeriesEmbedding f))=
      logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (PowerSeries.map phi f)) := by
  rw [actualPowerSeries_log_embedding,actualPowerSeries_log_embedding]
  apply HahnSeries.ext
  funext n
  change (Polynomial.C (((f:LaurentSeries K)).coeff n)).map phi=
    Polynomial.C (((PowerSeries.map phi f:PowerSeries L):LaurentSeries L).coeff n)
  rw [Polynomial.map_C,PowerSeries.coeff_coe,PowerSeries.coeff_coe]
  split_ifs <;> simp [PowerSeries.coeff_map]

/-- The literal generalized-log Euler equation transports to the exact
mapped matrix used by the constructed finite splitting frame. -/
theorem actualEuler_solution_field_map {r : ℕ} (phi : K →+* L)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (xi : K)
    (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j) :
    ∀ i,twistedPolynomialCoefficientEuler (phi xi) (logCoefficientFieldHom phi (u i))=
      ∑ j,logPolynomialToCoefficientSeries
        (logPowerSeriesEmbedding ((C.map (PowerSeries.map phi)) i j))*logCoefficientFieldHom phi (u j) := by
  intro i
  rw [← actualEuler_field_map,hu i,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,actualPowerSeries_log_field_map]
  rfl

end StrictEUnit
end
