import SelectedFourierExponentArithmetic
import Stage41SameSelectedAnalyticEuler
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- The original input now gives binomial arithmetic for ALL actual Fourier
indicial roots and for the SAME existing Fin nu exponent/amplitude witnesses.
This does not assert rationality, represented solutions or amplitude arithmetic. -/
theorem stage41_same_selected_fourier_exponent_arithmetic
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
      @SelectedFourierExponentArithmeticData F _ hNF (algebraMap F AlgebraicComplex) n T UI := by
  obtain ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic⟩ :=
    stage41_same_selected_analyticEuler a ha hne
  letI : NumberField F := hNF
  have hAll := selectedFuchsSourceData_fourier_indicial_root_arithmetic
    (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
    (algebraMap F AlgebraicComplex) n hr c T UI E hsource
  have hFourier := selectedFourierTwistedAmplitudeData_with_exponent_arithmetic
    (algebraMap F AlgebraicComplex) n T UI htwisted hAll
  exact ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,htwisted,hshear,hsourcearith,hanalytic,hAll,hFourier⟩

end StrictEUnit
end
