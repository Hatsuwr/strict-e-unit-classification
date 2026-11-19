import Stage41SameSelectedRegularPathContinuation
import SelectedFirstNuBoundaryData
import SelectedActualAnalyticGerms
import SelectedActualPathContinuation
import SelectedRegularResidueArithmetic

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original input keeps SAME witnesses and all prior packets, with the
derived ordinary-zero / regular-residue-binomial-arithmetic alternative. -/
theorem stage41_same_selected_regular_residue_arithmetic
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
      @SameClearingRegularResidueArithmeticData F _ hNF n T UI E := by
  obtain ⟨F,hmem,hNF,r,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath⟩ :=
    stage41_same_selected_actual_germs_and_regular_path_continuation a ha hne
  letI : NumberField F := hNF
  cases r with
  | zero => omega
  | succ n =>
    exact ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hfamily,hboundary,hactual,hpath,
      selectedFuchsSourceData_regular_residue_arithmetic
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
        (algebraMap F AlgebraicComplex) n hr c T UI E hsource⟩

end StrictEUnit
end
