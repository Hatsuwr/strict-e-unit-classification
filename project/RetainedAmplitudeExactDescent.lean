import FourierFrobeniusCoefficientField
import Stage38SeriesCoefficientExtension

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Restrict the actual coefficient sequence, preserving its Laurent support. -/
def laurentRestrictToField (F : IntermediateField ℚ K) (u : LaurentSeries K)
    (hu : ∀ n,u.coeff n∈F) : LaurentSeries F where
  coeff n :=⟨u.coeff n,hu n⟩
  isPWO_support' :=u.isPWO_support.mono (by
    intro n hn
    change u.coeff n≠0
    intro hz
    apply hn
    apply Subtype.ext
    exact hz)

theorem laurentRestrictToField_map (F : IntermediateField ℚ K) (u : LaurentSeries K)
    (hu : ∀ n,u.coeff n∈F) :
    stage38_laurentMap (algebraMap F K) (laurentRestrictToField F u hu)=u := by
  apply HahnSeries.ext
  funext n
  rfl

/-- Literal finite-log restriction, not a replacement Frobenius solution. -/
def logPolynomialRestrictToField (F : IntermediateField ℚ K)
    (p : Polynomial (LaurentSeries K)) (hp : ∀ j n,(p.coeff j).coeff n∈F) :
    Polynomial (LaurentSeries F) :=
  ∑ j ∈ p.support,Polynomial.monomial j (laurentRestrictToField F (p.coeff j) (hp j))

theorem logPolynomialRestrictToField_map (F : IntermediateField ℚ K)
    (p : Polynomial (LaurentSeries K)) (hp : ∀ j n,(p.coeff j).coeff n∈F) :
    stage38_logMap (algebraMap F K) (logPolynomialRestrictToField F p hp)=p := by
  change (logPolynomialRestrictToField F p hp).map (stage38_laurentMap (algebraMap F K))=p
  simp only [logPolynomialRestrictToField,Polynomial.map_sum,Polynomial.map_monomial,
    laurentRestrictToField_map]
  simpa only [Polynomial.sum_def] using Polynomial.sum_monomial_eq p

/-- The single finite coefficient field now contains literal lifts of the
EXACT retained amplitudes and exponents, with proved map-back identities. -/
theorem retainedFourierAmplitude_exact_common_field {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j))
    (F : IntermediateField ℚ AlgebraicComplex) (hF : FiniteDimensional ℚ F) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      ∃ AE : Fin (mu+1) →Fin (nu+1) →E,∃ rhoE : Fin nu →E,
      ∃ pE : Fin nu →Polynomial (LaurentSeries E),
        (∀ i j,algebraMap E AlgebraicComplex (AE i j)=A i j) ∧
        (∀ i,algebraMap E AlgebraicComplex (rhoE i)=rho i) ∧
        ∀ i,stage38_logMap (algebraMap E AlgebraicComplex) (pE i)=p i := by
  obtain ⟨E,hE,hFE,hA,hr,hB,hcoeff⟩ := fourierAmplitudeCoefficientFieldData A F hF hf e rho p hrho hp
  exact ⟨E,hE,hFE,(fun i j =>⟨A i j,hA i j⟩),(fun i =>⟨rho i,hr i⟩),
    (fun i =>logPolynomialRestrictToField E (p i) (hcoeff i)),
    (fun i j =>rfl),(fun i =>rfl),(fun i =>logPolynomialRestrictToField_map E (p i) (hcoeff i))⟩

end StrictEUnit
end
