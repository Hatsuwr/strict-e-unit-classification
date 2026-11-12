import ExtendedSourceCompanion
import HomogeneousSourceFrameArithmetic
import ActualParallelPreimageExtraction
import ActualFiniteLaurentArithmeticFrame

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Actual noninteger-class preimages over an enlarged number field inherit full
prefix arithmetic from the ORIGINAL selected-source hypotheses. The finite
splitting frame, its field, and all gauge arithmetic are derived internally. -/
theorem selectedFuchsSourceData_extended_actual_noninteger_preimage_arithmetic
    (psi : K →+* L)
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (rho : L) (hni : ∀ z : ℤ,rho≠(z:L))
    (f : Polynomial (LaurentSeries L))
    (hf :
      let t := (T.map (algebraMap (𝓞 K) K)).map psi
      let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial L) :=fun i j =>((UI i j).map (algebraMap (𝓞 K) K)).map psi
      let q := ordinaryReflectionTuple (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U)
      actualTwistedStage53Action rho (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) f=0) :
    ∃ u : LaurentSeries (Polynomial L),
      generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) u=logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree) ∧ LogSeriesPrefixArithmetic u := by
  let tK := T.map (algebraMap (𝓞 K) K)
  let UK : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
  let t := tK.map psi
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial L) :=fun i j =>(UK i j).map psi
  let cL := extendedSourceCompanion psi n tK UK
  let q := ordinaryReflectionTuple (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U)
  have hframe := selectedFuchsSourceData_extended_residual_frame psi G a phi n hr c T UI E hsource
  obtain ⟨hdata,hTK,hclearK,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hVK := companion_common_denominators_local_bounds n c tK UK hTK hclearK E hE hden
  have hT : t≠0 := (Polynomial.map_ne_zero_iff psi.injective).mpr hTK
  have hclear := extendedSourceCompanion_clearing psi n c tK UK hTK hclearK
  have hV := extendedSourceCompanion_valuation psi n tK UK hVK
  obtain ⟨u,hu,hdeg,hsol⟩ := actualStage53_noninteger_original_euler_solution rho hni n cL t U hT hclear hV f hf
  refine ⟨u,hu,hdeg,?_⟩
  let x := fun i : Fin (n+1) =>HahnSeries.single ((t.natTrailingDegree+i.val:ℕ):ℤ)
    (1:Polynomial L)*generalizedLogOrdinaryJet rho n
      (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u)) i
  let C := sourceLaurentEulerBase n t U 0
  have hx : ∀ i,twistedPolynomialCoefficientEuler rho (x i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*x j := by
    intro i
    rw [← twistedLogCoefficientEuler_eq]
    simpa only [actualPowerSeries_log_embedding] using hsol i
  have hf0 : FiniteSplittingUnfilteredFrameData (forcingEulerBlock C
      (augmentedSourceEulerColumn n t) (PowerSeries.C L (n+1))) := by
    simpa [finiteLaurentOffset,finiteLaurentEulerMatrix] using hframe 0 0
  have ha := homogeneousSource_from_extension_arithmetic C (augmentedSourceEulerColumn n t)
    (PowerSeries.C L (n+1)) hf0 rho x hx
  have hi := ha 0
  dsimp [x,generalizedLogOrdinaryJet] at hi
  rw [logLaurentCoefficientMap_reciprocalZ] at hi
  simpa only [Nat.add_zero] using
    logSeriesPrefixArithmetic_undo_reflected_gauge u ((t.natTrailingDegree+0:ℕ):ℤ) (-1) hi

end StrictEUnit
end
