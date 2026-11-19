import FrobeniusLeadingJetMatrix
import RegularLaurentDeterminantLeading
import FrobeniusIntegerShiftIndependence

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The actual companion jet of the retained Frobenius construction, not an
arbitrarily postulated solution frame. -/
def frobeniusActualJetMatrix {r : ℕ} (B : ℕ → Polynomial K)
    (e : frobeniusRootSeedIndex (B 0) ≃ Fin r) :
    Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)) := fun i j =>
  (twistedLogPolynomialEuler (frobeniusRootSeedExponent (B 0) (e.symm j)))^[i.val]
    (polynomialLogFrobeniusAmplitude B
      (frobeniusRootSeedExponent (B 0) (e.symm j))
      (frobeniusRootSeedPolynomial (B 0) (e.symm j)))

theorem frobeniusActualJetMatrix_coeff_zero {r : ℕ} (B : ℕ → Polynomial K)
    (e : frobeniusRootSeedIndex (B 0) ≃ Fin r) (i j : Fin r) :
    (logPolynomialToCoefficientSeries (frobeniusActualJetMatrix B e i j)).coeff 0=
      (shiftedPolynomialDerivative (frobeniusRootSeedExponent (B 0) (e.symm j)))^[i.val]
        (frobeniusRootSeedPolynomial (B 0) (e.symm j)) := by
  rw [frobeniusActualJetMatrix,logPolynomialToCoefficientSeries_twistedEuler_iterate,
    twistedPolynomialCoefficientEuler_iterate_coeff,Int.cast_zero,add_zero]
  congr 1
  apply Polynomial.ext
  intro t
  rw [logPolynomialToCoefficientSeries_double_coeff,polynomialLogFrobeniusAmplitude_seed_coeff]

theorem frobeniusActualJetMatrix_negative_coeff {r : ℕ} (B : ℕ → Polynomial K)
    (e : frobeniusRootSeedIndex (B 0) ≃ Fin r) (i j : Fin r) (a : ℤ) (ha : a<0) :
    (logPolynomialToCoefficientSeries (frobeniusActualJetMatrix B e i j)).coeff a=0 := by
  rw [frobeniusActualJetMatrix,logPolynomialToCoefficientSeries_twistedEuler_iterate,
    twistedPolynomialCoefficientEuler_iterate_coeff]
  have hz : (logPolynomialToCoefficientSeries (polynomialLogFrobeniusAmplitude B
      (frobeniusRootSeedExponent (B 0) (e.symm j))
      (frobeniusRootSeedPolynomial (B 0) (e.symm j)))).coeff a=0 := by
    apply Polynomial.ext
    intro t
    rw [logPolynomialToCoefficientSeries_double_coeff,
      polynomialLogFrobeniusAmplitude_negative_coeff _ _ _ a ha t,Polynomial.coeff_zero]
  rw [hz,iterate_map_zero]

/-- The determinant is genuinely nonzero. Its Laurent/log constant coefficient
is the proved invertible Hermite jet matrix. No scalar independence or assumed
fundamental matrix is substituted for this determinant argument. -/
theorem frobeniusActualJetMatrix_det_ne_zero {r : ℕ} (B : ℕ → Polynomial K)
    (hB : (B 0).Splits (RingHom.id K))
    (e : frobeniusRootSeedIndex (B 0) ≃ Fin r) :
    (frobeniusActualJetMatrix B e).det≠0 := by
  let H := (logPolynomialToCoefficientSeries (K:=K)).mapMatrix (frobeniusActualJetMatrix B e)
  have hH : ∀ i j a,a<0 →(H i j).coeff a=0 :=
    frobeniusActualJetMatrix_negative_coeff B e
  have hconst : Polynomial.constantCoeff (H.det.coeff 0)=(frobeniusLeadingJetMatrix (B 0) e).det := by
    rw [regularLaurentMatrix_det_coeff_zero H hH,RingHom.map_det]
    congr 1
    funext i j
    change ((logPolynomialToCoefficientSeries (frobeniusActualJetMatrix B e i j)).coeff 0).coeff 0=_
    rw [frobeniusActualJetMatrix_coeff_zero]
    rfl
  intro hz
  have hh := congrArg logPolynomialToCoefficientSeries hz
  rw [RingHom.map_det,map_zero] at hh
  change H.det=0 at hh
  have he : (frobeniusLeadingJetMatrix (B 0) e).det=0 := by
    rw [← hconst,hh,HahnSeries.coeff_zero,map_zero]
  exact frobeniusLeadingJetMatrix_det_ne_zero (B 0) hB e he

end StrictEUnit
end
