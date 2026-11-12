import SelectedFourierDenominatorSteps
import SelectedFourierRetainedArithmetic
import Stage41SameSelectedFourierUniformConjugates
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original a/ha/hne endpoint with every earlier witness and packet retained.
One common integer clears all shifted Fourier symbols. Beyond a derived
finite cutoff, exact powers of integer norms of indicial values propagate
coefficient denominators. The retained amplitudes additionally have proved joint exponential denominators and uniform conjugate growth. -/
theorem stage41_same_selected_fourier_retained_arithmetic
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
      @SameClearingFourierResonanceSolutionData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierFormalDimensionData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierNaturalBasisData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierLaurentRealizationData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierIntegerBasisData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierAmplitudeFieldData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierTriangularEstimateData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierAmplitudeGrowthData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierUniformConjugateData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierDenominatorStepData F _ hNF (algebraMap F AlgebraicComplex) n T UI ∧
      @SameClearingFourierRetainedArithmeticData F _ hNF (algebraMap F AlgebraicComplex) n T UI := by
  obtain ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier,hjoint,hblocks,hresonance,hdimension,hnatural,hlaurent,hinteger,hfield,htriangular,hgrowth,huniform⟩ :=
    stage41_same_selected_fourier_uniform_conjugates a ha hne
  letI : NumberField F := hNF
  exact ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier,hjoint,hblocks,hresonance,hdimension,hnatural,hlaurent,hinteger,hfield,htriangular,hgrowth,huniform,
    selectedFuchsSourceData_fourier_denominator_steps _ a
      (algebraMap F AlgebraicComplex) n hr c T UI E hsource,
    selectedFuchsSourceData_fourier_retained_arithmetic _ a
      (algebraMap F AlgebraicComplex) n hr c T UI E hsource⟩

end StrictEUnit
end

#print axioms StrictEUnit.stage41_same_selected_fourier_retained_arithmetic
