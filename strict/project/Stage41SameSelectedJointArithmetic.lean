import Stage41SameSelectedFuchsSource
import OrdinaryPointJointArithmetic

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Original input gives the SAME selected source/Fourier endpoint and joint
strict-E arithmetic of the RAW ordinary fundamental coefficient sequences.
The full represented Fin nu Fourier family remains a separate theorem. -/
theorem stage41_same_selected_source_and_joint_arithmetic
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
      @SameClearingOrdinaryArithmeticData F _ hNF r
        (minimalDerivativeCompanion r c) T UI E (algebraMap F AlgebraicComplex) := by
  obtain ⟨F,hmem,hNF,r,hr,c,T,UI,E,hpacket⟩ :=
    stage41_same_selected_regular_companion a ha hne
  letI : NumberField F := hNF
  refine ⟨F,hmem,hNF,r,hr,c,T,UI,E,?_,?_⟩
  · exact selectedRegularCompanionData_fuchs_source
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) a
      (algebraMap F AlgebraicComplex) r hr c T UI E hpacket
  · exact selectedRegularCompanionData_joint_arithmetic
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) (PowerSeries.mk a)
      (algebraMap F AlgebraicComplex) r hr c T UI E (algebraMap F AlgebraicComplex) hpacket

end StrictEUnit
end
