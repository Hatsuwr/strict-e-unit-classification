import SelectedFourierIntegerBasis
import Stage41SameSelectedFourierLaurentRealization
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original a/ha/hne endpoint with every v96 witness and packet retained.
One fixed all-integer-resonance family is an actual basis of BOTH full Laurent
coefficient and literal polynomial-log solution spaces. Dimensions equal the
integer resonance cost; all solutions have unique finite expansions. The exact
retained Fourier family is preserved. External exponents, arithmetic,
convergence and lifting remain separate obligations. -/
theorem stage41_same_selected_fourier_integer_basis
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
      @SameClearingFourierIntegerBasisData F _ hNF (algebraMap F AlgebraicComplex) n T UI := by
  obtain ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier,hjoint,hblocks,hresonance,hdimension,hnatural,hlaurent⟩ :=
    stage41_same_selected_fourier_laurent_realization a ha hne
  letI : NumberField F := hNF
  exact ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier,hjoint,hblocks,hresonance,hdimension,hnatural,hlaurent,
    selectedFuchsSourceData_fourier_integer_basis _ a
      (algebraMap F AlgebraicComplex) n hr c T UI E hsource⟩

end StrictEUnit
end

#print axioms StrictEUnit.stage41_same_selected_fourier_integer_basis
