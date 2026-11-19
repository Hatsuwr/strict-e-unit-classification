import Stage41SameSelectedActualAnalyticGerms
import SelectedFirstNuBoundaryData
import SelectedActualAnalyticGerms
import SelectedActualPathContinuation

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original strict-E input retains SAME witnesses and all prior packets,
now with actual arbitrary-germ regular-path continuation of its literal
clearing system. Singular-center arithmetic normalization remains separate. -/
theorem stage41_same_selected_actual_germs_and_regular_path_continuation
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex,
    ∃ hmem : ∀ n, a n ∈ F, ∃ hNF : NumberField F,
    ∃ r : ℕ, ∃ hr : 0 < r, ∃ c : Fin r → RatFunc F,
    ∃ T : Polynomial (𝓞 F),
    ∃ UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 F)), ∃ E : ℝ,
      @SelectedFuchsSourceData F _ hNF
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
        (algebraMap F AlgebraicComplex) r hr c T UI E ∧
      @SameClearingTranslatedScalarFamilyData F _ hNF r hr c
        T UI E (algebraMap F AlgebraicComplex) ∧
      @SelectedFirstNuBoundaryData F _ hNF a
        (algebraMap F AlgebraicComplex) r hr T UI ∧
      @SameClearingActualAnalyticGermsData F _ hNF r hr c
        T UI E (algebraMap F AlgebraicComplex) ∧
      @SameClearingRegularPathContinuationData F _ hNF r T UI := by
  obtain ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual⟩ :=
    stage41_same_selected_source_boundary_and_actual_germs a ha hne
  letI : NumberField F := hNF
  exact ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,
    sameClearing_regularPathContinuationData T UI⟩

end StrictEUnit
end
