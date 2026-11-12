import Stage41SameSelectedAllIndicialRootArithmetic
import SelectedFirstNuBoundaryData
import SelectedActualAnalyticGerms
import SelectedActualPathContinuation
import SelectedRegularResidueArithmetic
import SelectedIndicialRootArithmetic
import SelectedConstructedTwistedAmplitudes

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original inputs construct counted formal Fourier twisted amplitudes,
retaining all SAME witnesses and prior packets. This is not yet a represented
arithmetic ramified solution basis or singular analytic comparison. -/
theorem stage41_same_selected_constructed_twisted_amplitudes
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
      @SelectedFourierTwistedAmplitudeData F _ hNF (algebraMap F AlgebraicComplex) (n+1) hr T UI := by
  obtain ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots⟩ :=
    stage41_same_selected_all_indicial_root_arithmetic a ha hne
  letI : NumberField F := hNF
  exact ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,hresidue,hroots,
    selectedFuchsSourceData_constructed_twisted_amplitudes
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
      (algebraMap F AlgebraicComplex) (n+1) hr c T UI E hsource⟩

end StrictEUnit
end
