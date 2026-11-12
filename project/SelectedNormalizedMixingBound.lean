import NormalizedMixingMatrixBound

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Exponent arithmetic for the exact common-field lifts is derived from the
original source and reflected indicial equation, not supplied as a new premise. -/
theorem selectedFuchsSourceData_lifted_exponent_binomial_arithmetic
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (B : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI B)
    (q : Fin (n+2) →Polynomial AlgebraicComplex)
    (hq : q=ordinaryReflectionTuple (n+1) (fun i =>
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n)
        (T.map (algebraMap (𝓞 K) K))
        (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) i).map phi))
    (hf : Stage56FiniteFuchs (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q))
    (chi : L →+* AlgebraicComplex)
    (rhoL : Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q) →L)
    (hroot : ∀ i,(sameFourierEulerCoefficientSymbols _ hf 0).eval (chi (rhoL i))=0) :
    JointBinomialPrefixDenominators rhoL := by
  apply jointBinomialPrefixDenominators_of_map chi rhoL
  have hAll := selectedFuchsSourceData_fourier_indicial_root_arithmetic
    G a phi n hr c T UI B hsource
  have hJoint := sameClearingFourierIndicialArithmeticData_joint phi n T UI hAll
  subst q
  exact hJoint hf (fun i =>chi (rhoL i)) hroot

end StrictEUnit
end
