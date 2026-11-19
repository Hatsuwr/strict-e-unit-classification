import ExtendedSourceCompanion
import FiniteSplittingActualSolutionArithmetic
import ActualParallelPreimageExtraction
import ActualFiniteLaurentArithmeticFrame

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Actual zero-class preimages over an enlarged number field inherit full
prefix arithmetic from the ORIGINAL selected-source hypotheses. The finite
splitting frame, its field, and all gauge arithmetic are derived internally. -/
theorem selectedFuchsSourceData_extended_actual_zero_preimage_arithmetic
    (psi : K →+* L)
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (f : Polynomial (LaurentSeries L))
    (hf :
      let t := (T.map (algebraMap (𝓞 K) K)).map psi
      let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial L) :=fun i j =>((UI i j).map (algebraMap (𝓞 K) K)).map psi
      let q := ordinaryReflectionTuple (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U)
      actualTwistedStage53Action 0 (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) f=0) :
    ∃ u : LaurentSeries (Polynomial L),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree+1) ∧ LogSeriesPrefixArithmetic u := by
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
  obtain ⟨u,hu,hdeg,P,hsol⟩ := actualStage53_zero_original_euler_solution n cL t U hT hclear hV f hf
  refine ⟨u,hu,hdeg,?_⟩
  let d := reciprocalCommonDegree (n+1) q
  let k := fun j : ℕ =>(d:ℤ)-(j:ℤ)
  let M := finiteLaurentOffset k (P.natDegree+1)
  let w := fun i : Fin (n+1) =>M+t.natTrailingDegree+i.val
  let v := parallelForcingVector (generalizedLogOrdinaryJet 0 n
    (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u)))
    (reflectedResidualConstant d P) (P.natDegree+1)
  let x := fun i =>HahnSeries.single (finiteLaurentEulerWeights w (M+(n+1)) k (P.natDegree+1) i:ℤ)
    (1:Polynomial L)*v i
  let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n t U M)
    (augmentedSourceEulerColumn n t) (M+(n+1)) k (P.natDegree+1)
  have hx : ∀ i,twistedPolynomialCoefficientEuler 0 (x i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*x j := by
    intro i
    rw [← twistedLogCoefficientEuler_eq]
    simpa only [actualPowerSeries_log_embedding] using hsol i
  have ha := finiteSplittingFrame_actual_solution_arithmetic C (hframe d P.natDegree) 0 x hx
  exact actualParallelPreimage_extract_arithmetic 0 n (P.natDegree+1) u
    (reflectedResidualConstant d P) w (M+(n+1)) k ha

end StrictEUnit
end
