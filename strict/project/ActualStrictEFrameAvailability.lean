import SelectedFourierActualNormalForm
import Stage41SameSelectedScalarNormalForm
import Stage41StrictSeriesCorrespondence
noncomputable section
namespace StrictEUnit

theorem actualStrictE_scalarNormalFormAvailability :
    Stage33NonzeroScalarNormalFormAvailability := by
  intro f hf hne
  obtain ⟨a,hent,hs,hop,harith⟩ := hf
  have hf : IsStrictEFunction f := ⟨a,hent,hs,hop,harith⟩
  have ha := stage41_actualStrictE_isStrictESeries hf a hs
  have hcoeff : ∃ n, a n ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    funext z
    have hz := hs z
    simp only [h, ZeroMemClass.coe_zero, zero_mul, zero_div] at hz
    exact hz.unique hasSum_zero
  obtain ⟨F,hmem,hNF,n,hr,c,T,UI,E,hsource,hrest⟩ :=
    stage41_same_selected_fourier_scalarNormalForm a ha hcoeff
  letI : NumberField F := hNF
  obtain ⟨m,r,b,p,hm,hode,hS⟩ :=
    selectedFuchsSourceData_actual_scalarNormalForm _ a
      (algebraMap F AlgebraicComplex) n hr c T UI E hsource harith
  have heq := stage41_strictSeriesFunction_eq_of_representation harith f hs
  rw [heq] at hode
  exact ⟨m,r,b,p,hode,hS⟩

theorem actualStrictE_commonArithmeticFrameAvailability :
    StrictECommonArithmeticFrameAvailability :=
  stage33_commonFrameAvailability_of_scalarNormalForm actualStrictE_scalarNormalFormAvailability

end StrictEUnit
