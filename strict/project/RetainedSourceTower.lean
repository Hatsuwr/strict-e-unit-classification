import RetainedAmplitudeExactDescent
import ReciprocalArrayFieldMap

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- The original source image is a finite intermediate field. -/
theorem sourceEmbedding_finite_image (phi : K →+* AlgebraicComplex) :
    FiniteDimensional ℚ phi.toRatAlgHom.fieldRange := by
  exact FiniteDimensional.of_surjective phi.toRatAlgHom.rangeRestrict.toLinearMap
    phi.toRatAlgHom.rangeRestrict_surjective

/-- An inclusion of the source image gives the actual source embedding into E. -/
def sourceEmbeddingInto (phi : K →+* AlgebraicComplex)
    (E : IntermediateField ℚ AlgebraicComplex) (h : phi.toRatAlgHom.fieldRange ≤ E) : K →+* E where
  toFun x := ⟨phi x,h ⟨x,rfl⟩⟩
  map_one' := Subtype.ext (map_one phi)
  map_mul' x y := Subtype.ext (map_mul phi x y)
  map_zero' := Subtype.ext (map_zero phi)
  map_add' x y := Subtype.ext (map_add phi x y)

theorem sourceEmbeddingInto_tower (phi : K →+* AlgebraicComplex)
    (E : IntermediateField ℚ AlgebraicComplex) (h : phi.toRatAlgHom.fieldRange ≤ E) :
    (algebraMap E AlgebraicComplex).comp (sourceEmbeddingInto phi E h)=phi := by
  ext x
  rfl

/-- The retained family and the entire original source field share a finite
field, with a proved tower identity rather than an assumed source inclusion. -/
theorem retainedFourierAmplitude_source_tower {mu nu : ℕ}
    (phi : K →+* AlgebraicComplex)
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j)) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧
      ∃ psi : K →+* E,(algebraMap E AlgebraicComplex).comp psi=phi ∧
      ∃ AE : Fin (mu+1) →Fin (nu+1) →E,∃ rhoE : Fin nu →E,
      ∃ pE : Fin nu →Polynomial (LaurentSeries E),
        (∀ i j,algebraMap E AlgebraicComplex (AE i j)=A i j) ∧
        (∀ i,algebraMap E AlgebraicComplex (rhoE i)=rho i) ∧
        ∀ i,stage38_logMap (algebraMap E AlgebraicComplex) (pE i)=p i := by
  obtain ⟨E,hE,hFE,AE,rhoE,pE,hA,hr,hpE⟩ :=
    retainedFourierAmplitude_exact_common_field A hf e rho p hrho hp
      phi.toRatAlgHom.fieldRange (sourceEmbedding_finite_image phi)
  exact ⟨E,hE,sourceEmbeddingInto phi E hFE,sourceEmbeddingInto_tower phi E hFE,
    AE,rhoE,pE,hA,hr,hpE⟩
end StrictEUnit
end
