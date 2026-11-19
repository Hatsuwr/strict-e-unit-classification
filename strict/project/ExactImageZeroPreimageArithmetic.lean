import ActualSourceTowerEquation
import ExtendedActualZeroPreimageArithmetic

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

theorem selectedFuchsSourceData_exact_image_zero_preimage_arithmetic
    (psi : K →+* L) (chi : L →+* AlgebraicComplex)
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (htower : chi.comp psi=phi)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (f : Polynomial (LaurentSeries L))
    (fC : Polynomial (LaurentSeries AlgebraicComplex))
    (hfC : stage38_logMap chi f=fC)
    (hf :
      let t := T.map (algebraMap (𝓞 K) K)
      let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
      let q := ordinaryReflectionTuple (n+1) (fun i =>(sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U i).map phi)
      actualTwistedStage53Action 0 (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) fC=0) :
    ∃ u : LaurentSeries (Polynomial L),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree+1) ∧ LogSeriesPrefixArithmetic u := by
  apply selectedFuchsSourceData_extended_actual_zero_preimage_arithmetic
    psi G a phi n hr c T UI E hsource f
  exact actualRetained_source_tower_equation psi chi phi htower (n+1) (Nat.succ_pos n)
    (T.map (algebraMap (𝓞 K) K))
    (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) 0 0 (map_zero chi) f fC hfC hf

end StrictEUnit
end
