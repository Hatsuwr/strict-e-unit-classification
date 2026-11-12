import Stage41SameSelectedRegularCompanion
import SelectedFuchsSourceData

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Exact original-input selected-source conclusion, with every original conjunct
retained in SelectedFuchsSourceData and no source-family premise. -/
theorem stage41_same_selected_fuchs_source_and_fourier
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex,
    ∃ hmem : ∀ n, a n ∈ F, ∃ hNF : NumberField F,
    ∃ r : ℕ, ∃ hr : 0 < r, ∃ c : Fin r → RatFunc F,
    ∃ T : Polynomial (𝓞 F),
    ∃ UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 F)), ∃ E : ℝ,
      @SelectedFuchsSourceData F _ hNF
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
        (algebraMap F AlgebraicComplex) r hr c T UI E := by
  obtain ⟨F,hmem,hNF,r,hr,c,T,UI,E,hpacket⟩ :=
    stage41_same_selected_regular_companion a ha hne
  letI : NumberField F := hNF
  exact ⟨F,hmem,hNF,r,hr,c,T,UI,E,
    selectedRegularCompanionData_fuchs_source
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
      (algebraMap F AlgebraicComplex) r hr c T UI E hpacket⟩

end StrictEUnit
end
