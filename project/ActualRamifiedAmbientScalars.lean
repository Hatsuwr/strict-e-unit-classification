import ScalarIndependenceFromJets
import RamifiedScalarEulerEquation
noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem actualFourier_ramified_ambient_independent {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → K) (p : Fin nu → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (N : ℕ) (hN : N ≠ 0) (m : Fin nu → ℤ)
    (hm : ∀ j, (m j : K) / (N : K) = rho j) :
    LinearIndependent K (fun j => stage38_logAmbient
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j))) := by
  apply stage38_logAmbient_linearIndependent
  have h := actualFourier_ramified_scalar_independent A hf e rho p hrho hp N hN m hm
  simpa only [stage38_logModule_eq] using h

theorem sourceEmbedding_identity (k : Subfield ℂ)
    (p : Polynomial (LaurentSeries k)) :
    stage38_sourceEmbedding (RingHom.id k) p = stage38_logAmbient p := by
  change stage38_logAmbient (stage38_logMap (RingHom.id k) p) = _
  congr 1
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  simp [stage38_logMap_coeff, stage38_laurentMap_coeff]

theorem actualFourier_ramified_ambient_equation (k : Subfield ℂ) {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → k) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (N : ℕ) (hN : N ≠ 0) (m : ℤ)
    (hm : (m : k) / (N : k) = frobeniusRootSeedExponent _ i) :
    ∑ l : Fin (nu+1), Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))
      (stage53_fourierCoeff A l) *
      (stage32_ramifiedOrdinaryDerivation k N hN : RatFunc (LaurentSeries k) → _)^[l.val]
        (stage38_logAmbient (Polynomial.C (HahnSeries.single m (1 : k)) *
          stage38_logRamification N hN (sameFourierTwistedAmplitude A hf i))) = 0 := by
  have h := stage38_sourceEmbedding_ordinary_equation k (RingHom.id k) N hN nu
    (stage53_fourierCoeff A) _
    (actualFourier_ramified_ordinary_equation A hf hc i N hN m hm)
  simpa only [Polynomial.map_id, sourceEmbedding_identity] using h
end StrictEUnit
end
