import ActualFiniteLaurentConstructedFrame
import FiniteSplittingUnfilteredFrame
import SelectedFiniteLaurentUnitEulerArithmetic

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem regularEulerGauge_compose {r : ℕ}
    (A B C G H S T : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hGH : G*H=1) (hHG : H*G=1) (hST : S*T=1) (hTS : T*S=1)
    (hG : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*A=B*G)
    (hS : Matrix.of (fun i j =>powerSeriesEuler (S i j))+S*B=C*S) :
    (S*G)*(H*T)=1 ∧ (H*T)*(S*G)=1 ∧
      Matrix.of (fun i j =>powerSeriesEuler ((S*G) i j))+(S*G)*A=C*(S*G) := by
  have hinv : (S*G)*(H*T)=1 := by rw [mul_assoc S G,← mul_assoc G H,hGH,one_mul,hST]
  have hinv' : (H*T)*(S*G)=1 := by rw [mul_assoc H T,← mul_assoc T S,hTS,one_mul,hHG]
  refine ⟨hinv,hinv',?_⟩
  let D : Derivation K (PowerSeries K) (PowerSeries K) := (PowerSeries.X : PowerSeries K) • PowerSeries.derivative K
  change matrixDerivative D (S*G)+(S*G)*A=C*(S*G)
  change matrixDerivative D G+G*A=B*G at hG
  change matrixDerivative D S+S*B=C*S at hS
  have hg : matrixDerivative D G=B*G-G*A := eq_sub_iff_add_eq.mpr hG
  have hs : matrixDerivative D S=C*S-S*B := eq_sub_iff_add_eq.mpr hS
  rw [matrixDerivative_mul,hg,hs]
  noncomm_ring

/-- Constructed scalar gauge for the actual finite Laurent system, before any
splitting or arithmetic conclusion. The composite gauge is explicitly proved. -/
theorem actualFiniteLaurentSource_scalarGauge
    (n s M L : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (k : ℕ →ℤ)
    (hinj : Function.Injective (fun j : Fin (s+1) =>(((L:ℤ)+k j.val):K))) :
    let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) L k (s+1)
    ∃ b : Fin (((n+1)+(s+1))+1) →PowerSeries K,
    ∃ G H : Matrix (Fin ((n+1)+(s+1))) (Fin ((n+1)+(s+1))) (PowerSeries K),
      b (Fin.last ((n+1)+(s+1)))=1 ∧ G*H=1 ∧ H*G=1 ∧
      Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=
        scalarEulerPowerSeriesCompanion ((n+1)+(s+1)) b*G := by
  intro C
  let lam : Fin (s+1) →K := fun j =>(((L:ℤ)+k j.val):K)
  obtain ⟨a,ha⟩ := forcingMoment_closure_coefficients lam hinj
  have hV : IsUnit (((forcingMomentMatrix lam).map (PowerSeries.C K)).det) := by
    change IsUnit (((PowerSeries.C K).mapMatrix (forcingMomentMatrix lam)).det)
    rw [← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr (forcingMomentMatrix_det_ne_zero lam hinj)).map (PowerSeries.C K)
  let e := orderedSystemGauge (n+1) (s+1) ((forcingMomentMatrix lam).map (PowerSeries.C K)) hV
  let G := LinearMap.toMatrix' e.toLinearMap
  let H := LinearMap.toMatrix' e.symm.toLinearMap
  obtain ⟨hg,hh⟩ := linearEquiv_matrix_twoSided e
  have hc := actualOrderedMoment_matrix_connection (sourceLaurentEulerBase n T U M)
    (augmentedSourceEulerColumn n T) L k lam a (fun j =>rfl) ha hV
  let B := orderedMomentConnection (sourceLaurentEulerBase n T U M)
    (augmentedSourceEulerColumn n T) (fun j =>PowerSeries.C K (a j))
  have hB : EulerCyclicShape B := by
    apply orderedMomentConnection_cyclicShape
    · exact sourceLaurentEulerBase_cyclicShape n T U M
    · intro i hi;rw [augmentedSourceEulerColumn,if_neg (by omega)]
    · exact augmentedSourceEulerColumn_unit n T hT
  obtain ⟨b,S,Q,hb,hdet,hSQ,hQS,hconn⟩ := cyclicShape_exists_scalarGauge B (by omega) hB
  exact ⟨b,S*G,H*Q,hb,regularEulerGauge_compose C B _ G H S Q hg hh hSQ hQS hc hconn⟩

end StrictEUnit
end
