import Stage41SameSelectedFirstNuBoundary
import SelectedFirstNuBoundaryData
import SelectedActualAnalyticGerms

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original input retains the SAME witnesses and prior packets, with actual
independent analytic starting germs at the very same arithmetic ordinary point.
No continuation to singular zero or represented Fourier family is asserted. -/
theorem stage41_same_selected_source_boundary_and_actual_germs
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
        T UI E (algebraMap F AlgebraicComplex) := by
  obtain ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily,hboundary⟩ :=
    stage41_same_selected_source_family_and_firstNu_boundary a ha hne
  letI : NumberField F := hNF
  refine ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily,hboundary,?_⟩
  exact sameClearingTranslatedScalarFamilyData_actual_analytic_germs
    r hr c T UI E (algebraMap F AlgebraicComplex) hsource.2.2.1 hfamily

end StrictEUnit
end
