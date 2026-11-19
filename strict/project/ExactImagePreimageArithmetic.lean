import ActualSourceTowerEquation
import ExtendedActualNonintegerPreimageArithmetic

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

theorem selectedFuchsSourceData_exact_image_noninteger_preimage_arithmetic
    (psi : K →+* L) (chi : L →+* AlgebraicComplex)
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (htower : chi.comp psi=phi)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (rho : L) (hni : ∀ z : ℤ,rho≠(z:L))
    (f : Polynomial (LaurentSeries L))
    (fC : Polynomial (LaurentSeries AlgebraicComplex))
    (hfC : stage38_logMap chi f=fC)
    (hf :
      let t := T.map (algebraMap (𝓞 K) K)
      let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
      let q := ordinaryReflectionTuple (n+1) (fun i =>(sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U i).map phi)
      actualTwistedStage53Action (chi rho) (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) fC=0) :
    ∃ u : LaurentSeries (Polynomial L),
      generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) u=logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree) ∧ LogSeriesPrefixArithmetic u := by
  apply selectedFuchsSourceData_extended_actual_noninteger_preimage_arithmetic
    psi G a phi n hr c T UI E hsource rho hni f
  exact actualRetained_source_tower_equation psi chi phi htower (n+1) (Nat.succ_pos n)
    (T.map (algebraMap (𝓞 K) K))
    (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) rho (chi rho) rfl f fC hfC hf

end StrictEUnit
end
