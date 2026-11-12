import FourierRetainedArithmeticPacket

noncomputable section
namespace StrictEUnit

/-- The packet implies the manuscript's literal strict-E ARITHMETIC predicate
for each log coefficient. A differential equation is not asserted here. -/
theorem fourierRetainedArithmeticData_strictEArithmetic {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A)
    (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i)) :
    ∀ i j,HasStrictEArithmetic (fun n =>logAmplitudeFactorialCoefficient (p i) j n) := by
  obtain ⟨E,hE,hFE,hA,hr,hcoeff,hfact,C,hC,hconj,hden⟩ :=
    ha (⊥ : IntermediateField ℚ AlgebraicComplex) inferInstance hf e rho p hrho hp
  choose D hD hDb hDi using hden
  intro i j
  refine ⟨C,hC,fun sigma n =>hconj sigma i j n,D,hD,hDb,?_⟩
  intro N m hm
  have hi := (hDi N i m hm j).map (algebraicClosure ℚ ℂ).val.toIntAlgHom
  simpa only [RingHom.toIntAlgHom_apply,map_mul,map_natCast] using hi
end StrictEUnit
end
