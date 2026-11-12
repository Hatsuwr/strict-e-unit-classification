import SelectedFourierResonanceSolutions
import Stage41SameSelectedFourierBlockIndependence
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- The original a/ha/hne endpoint retains every v92 witness and packet.
For every integer-difference class of the exact retained Fourier amplitudes,
it now derives integer Laurent shifts, independence and one common twisted
equation. External base exponents, rationality, cross-class representation,
full spanning, amplitude arithmetic and convergence remain unresolved. -/
theorem stage41_same_selected_fourier_resonance_solutions
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex,
    ∃ hmem : ∀ n, a n ∈ F, ∃ hNF : NumberField F,
    ∃ n : ℕ, ∃ hr : 0 < (n+1), ∃ c : Fin (n+1) → RatFunc F,
    ∃ T : Polynomial (𝓞 F),
    ∃ UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 F)), ∃ E : ℝ,
      @SelectedFuchsSourceData F _ hNF
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
        (algebraMap F AlgebraicComplex) (n+1) hr c T UI E ∧
      @SameClearingTranslatedScalarFamilyData F _ hNF (n+1) hr c
        T UI E (algebraMap F AlgebraicComplex) ∧
      @SelectedFirstNuBoundaryData F _ hNF a
        (algebraMap F AlgebraicComplex) (n+1) hr T UI ∧
      @SameClearingActualAnalyticGermsData F _ hNF (n+1) hr c
        T UI E (algebraMap F AlgebraicComplex) ∧
      @SameClearingRegularPathContinuationData F _ hNF (n+1) T UI ∧
      @SameClearingRegularResidueArithmeticData F _ hNF n T UI E ∧
      @SameClearingIndicialRootArithmeticData F _ hNF n T UI (algebraMap F AlgebraicComplex) ∧
      @SelectedFourierTwistedAmplitudeData F _ hNF (algebraMap F AlgebraicComplex) (n+1) hr T UI ∧
      @SameClearingDifferentialShearData F _ hNF
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) n T UI ∧
      @SameClearingSourceBoundaryArithmeticData F _ hNF n T UI
        (algebraMap F AlgebraicComplex) ∧
      @SameClearingAnalyticEulerData F _ hNF n T UI ∧
      @SameClearingFourierIndicialArithmeticData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SelectedFourierExponentArithmeticData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierJointBinomialData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierBlockIndependenceData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierResonanceSolutionData F _ hNF (algebraMap F AlgebraicComplex) n T UI := by
  obtain ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier,hjoint,hblocks⟩ :=
    stage41_same_selected_fourier_block_independence a ha hne
  letI : NumberField F := hNF
  exact ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier,hjoint,hblocks,
    selectedFuchsSourceData_fourier_resonance_solutions _ a
      (algebraMap F AlgebraicComplex) n hr c T UI E hsource⟩

end StrictEUnit
end

#print axioms StrictEUnit.stage41_same_selected_fourier_resonance_solutions
