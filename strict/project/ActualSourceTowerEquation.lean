import RetainedSourceTower
import ActualReciprocalFieldEquation

noncomputable section
namespace StrictEUnit
variable {K L M : Type*} [Field K] [Field L] [Field M] [CharZero L] [CharZero M]

theorem reflectedCompanion_source_tower (psi : K →+* L) (chi : L →+* M)
    (phi : K →+* M) (htower : chi.comp psi=phi)
    (r : ℕ) (hr : 0<r) (T : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) :
    ordinaryReflectionTuple r (fun i =>(sameCompanionScalarTuple r hr T U i).map phi)=
      fun i =>(ordinaryReflectionTuple r
        (sameCompanionScalarTuple r hr (T.map psi) (fun i j =>(U i j).map psi)) i).map chi := by
  funext i
  rw [ordinaryReflectionTuple_field_map]
  congr 1
  funext j
  rw [← sameCompanionScalarTuple_field_map,Polynomial.map_map,htower]

/-- Literal retained amplitude equations descend to the reflected mapped source
companion, using the actual tower and exact map-back amplitude and exponent. -/
theorem actualRetained_source_tower_equation (psi : K →+* L) (chi : L →+* M)
    (phi : K →+* M) (htower : chi.comp psi=phi)
    (r : ℕ) (hr : 0<r) (T : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (rho : L) (rhoM : M) (hrho : chi rho=rhoM)
    (f : Polynomial (LaurentSeries L)) (fM : Polynomial (LaurentSeries M))
    (hf : stage38_logMap chi f=fM)
    (hsol :
      let q := ordinaryReflectionTuple r
        (fun i =>(sameCompanionScalarTuple r hr T U i).map phi)
      actualTwistedStage53Action rhoM (reciprocalSourceArray r (reciprocalCommonDegree r q) q) fM=0) :
    let q := ordinaryReflectionTuple r
      (sameCompanionScalarTuple r hr (T.map psi) (fun i j =>(U i j).map psi))
    actualTwistedStage53Action rho (reciprocalSourceArray r (reciprocalCommonDegree r q) q) f=0 := by
  apply actualStage53_reciprocal_image_descent chi rho r _ _
    (reflectedCompanion_source_tower psi chi phi htower r hr T U) f fM hf
  rw [hrho]
  exact hsol
end StrictEUnit
end
