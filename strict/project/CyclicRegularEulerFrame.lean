import RegularEulerLogGauge
import AugmentedSourceCyclicShape
import FrobeniusCompanionFilteredArithmetic

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A positive cyclic-shaped system supplies a concrete monic scalar equation,
a unit-determinant jet change, its two-sided inverse and the exact connection identity. -/
theorem cyclicShape_exists_scalarGauge {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0<r) (hC : EulerCyclicShape C) :
    ∃ b : Fin (r+1) →PowerSeries K,∃ G H : Matrix (Fin r) (Fin r) (PowerSeries K),
      b (Fin.last r)=1 ∧ IsUnit G.det ∧ G*H=1 ∧ H*G=1 ∧
      Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G := by
  cases r with
  | zero =>omega
  | succ n =>
    have h := eulerCyclicJetMatrix_det_isUnit C hC.1 (fun i =>hC.2 i.castSucc i.succ rfl)
    exact ⟨eulerCyclicScalarTuple C,eulerCyclicJetMatrix C,(eulerCyclicJetMatrix C)⁻¹,
      eulerCyclicScalarTuple_top C,h,Matrix.mul_nonsing_inv _ h,Matrix.nonsing_inv_mul _ h,
      eulerCyclicCompanion_connection C h⟩

/-- Transfer an actual logarithmic frame backwards through the proved regular
scalar-jet change. Nonvanishing follows from the two-sided identity. -/
theorem regularEuler_log_frame_pullback {r : ℕ}
    (C B G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=B*G)
    (rho : Fin r →K) (Z : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hZ : ∀ j i,twistedLogPolynomialEuler (rho j) (Z i j)=
      ∑ l,logPowerSeriesEmbedding (B i l)*Z l j) (hdet : Z.det≠0) :
    let Y := H.map logPowerSeriesEmbedding*Z
    Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) := by
  dsimp only
  have hz : G.map logPowerSeriesEmbedding*(H.map logPowerSeriesEmbedding*Z)=Z := by
    change logPowerSeriesEmbedding.toRingHom.mapMatrix G*(logPowerSeriesEmbedding.toRingHom.mapMatrix H*Z)=Z
    rw [← mul_assoc,← map_mul,hGH,map_one,one_mul]
  constructor
  · intro h
    have he := congrArg Matrix.det hz
    rw [Matrix.det_mul,h,mul_zero] at he
    exact hdet he.symm
  · apply (regularEuler_log_frame_gauge_iff C B G H hHG hc rho _).mpr
    simpa only [hz] using hZ

/-- Once the ACTUAL scalar indicial polynomial splits, the matching frame is
constructed. Neither its solution identity nor its determinant is a hypothesis. -/
theorem regularScalarGauge_constructed_log_frame {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (b : Fin (r+1) →PowerSeries K)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G)
    (hsplit : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K)) :
    ∃ rho : Fin r →K,∃ Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)),
      Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
        ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) := by
  let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
  let e := scalarEulerFrobeniusIndexEquiv r b hb hsplit
  let rho : Fin r →K := fun j =>frobeniusRootSeedExponent (B 0) (e.symm j)
  let Z := frobeniusActualJetMatrix B e
  obtain ⟨hdet,hZ,hJ⟩ := scalarEuler_constructed_frobenius_frame r b hb hsplit
  exact ⟨rho,H.map logPowerSeriesEmbedding*Z,
    regularEuler_log_frame_pullback C _ G H hGH hHG hc rho Z hZ hdet⟩

/-- Reindex both the coordinates and frame columns without changing determinant. -/
theorem regularEuler_log_frame_reindex {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r →K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (e : Equiv.Perm (Fin r)) :
    ∀ j i,twistedLogPolynomialEuler (rho (e j)) ((Y.submatrix e e) i j)=
      ∑ l,logPowerSeriesEmbedding ((C.submatrix e e) i l)*(Y.submatrix e e) l j := by
  intro j i
  change twistedLogPolynomialEuler (rho (e j)) (Y (e i) (e j))=_
  rw [hY]
  exact (Equiv.sum_comp e (fun l =>logPowerSeriesEmbedding (C (e i) l)*Y l (e j))).symm

end StrictEUnit
end
