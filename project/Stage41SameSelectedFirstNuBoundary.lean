import Stage41SameSelectedTranslatedFamily
import SelectedFirstNuBoundaryData

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original input retains its full SAME source/Fourier and translated scalar
family packets, now with the exact first-nu initial boundary identities. -/
theorem stage41_same_selected_source_family_and_firstNu_boundary
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
        (algebraMap F AlgebraicComplex) r hr T UI := by
  obtain ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily⟩ :=
    stage41_same_selected_source_and_translated_scalar_family a ha hne
  letI : NumberField F := hNF
  refine ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily,?_⟩
  exact selectedFuchsSourceData_firstNu_boundary
    (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
    (algebraMap F AlgebraicComplex) r hr c T UI E hsource

end StrictEUnit
end
