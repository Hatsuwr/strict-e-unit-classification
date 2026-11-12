import FrobeniusFullLaurentRealization
import FourierNaturalResonanceBasis

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem frobeniusIntegerShift_add (k l : ℤ) (p : Polynomial (LaurentSeries K)) :
    frobeniusIntegerShift k (frobeniusIntegerShift l p) = frobeniusIntegerShift (k+l) p := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  simp only [frobeniusIntegerShift_coeff]
  congr 1
  omega

/-- Canonical Laurent normalization does not change the retained Fourier
family. The total shift is an actual integer, and its exponent identity is exact. -/
theorem normalizedLaurentAmplitude_retained_fourier_index
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (ξ : K) (s : LaurentSeries (Polynomial K))
    (i : polynomialLogResonanceCoordinateIndex (ξ+(s.order : K))
      (sameFourierEulerCoefficientSymbols A hf 0)) :
    ∃ j : Fin ν,rho j = ξ + ((s.order + (i.1.1 : ℤ) : ℤ) : K) ∧
      frobeniusIntegerShift s.order
        (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf)
          (ξ+(s.order : K)) i) = frobeniusIntegerShift (s.order+(i.1.1 : ℤ)) (p j) := by
  obtain ⟨j,hj,hp'⟩ := naturalResonanceFrobeniusAmplitude_retained_fourier_index
    A hf hc e rho p hrho hp (ξ+(s.order : K)) i
  refine ⟨j,?_,?_⟩
  · simpa only [Int.cast_add,Int.cast_natCast,add_assoc] using hj
  · rw [hp',frobeniusIntegerShift_add]

/-- Full actual Laurent coefficient solutions, including negative tails and
initially unbounded logarithms: uniform cutoff, unique literal realization,
and unique finite expansion after canonical integer normalization. -/
def FourierLaurentRealizationData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,∀ ξ : K,
  let B := sameFourierEulerCoefficientSymbols A hf
  let b := fun k : Fin (ν+1) => (stage61_fourierLift A hf).coeff k.val
  ∀ s : LaurentSeries (Polynomial K),scalarTwistedCoefficientOperator ν b ξ s = 0 →
  HasUniformLogBound s (2*ν) ∧
  (∃! p : Polynomial (LaurentSeries K),
    logPolynomialToCoefficientSeries p = s ∧ scalarTwistedLogOperator ν b ξ p = 0) ∧
  laurentCoefficientShift s.order
    ((PowerSeries.mk (laurentNormalizedCoefficients s) : PowerSeries (Polynomial K)) :
      LaurentSeries (Polynomial K)) = s ∧
  (∃! c : polynomialLogResonanceCoordinateIndex (ξ+(s.order : K)) (B 0) → K,
    laurentNormalizedCoefficients s = ∑ i,c i • naturalResonanceFrobeniusCoefficients
      B (ξ+(s.order : K)) i) ∧
  ∀ e : frobeniusRootSeedIndex (B 0) ≃ Fin ν,
  ∀ rho : Fin ν → K,∀ p : Fin ν → Polynomial (LaurentSeries K),
    (∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∀ i : polynomialLogResonanceCoordinateIndex (ξ+(s.order : K)) (B 0),
      ∃ j : Fin ν,rho j = ξ + ((s.order+(i.1.1 : ℤ) : ℤ) : K) ∧
        frobeniusIntegerShift s.order
          (naturalResonanceFrobeniusAmplitude B (ξ+(s.order : K)) i) =
            frobeniusIntegerShift (s.order+(i.1.1 : ℤ)) (p j)

theorem fourierLaurentRealizationData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierLaurentRealizationData A := by
  intro hf ξ
  dsimp only
  intro s hs
  have hP := sameFourierEulerIndicial_ne_zero A hf hc
  refine ⟨?_,polynomialLogLaurentSolution_existsUnique_realization ν _ ξ hP s hs,
    laurentNormalizedCoefficients_representation s,
    polynomialLogLaurentSolution_existsUnique_normalized_expansion ν _ ξ hP s hs,?_⟩
  · have hb := polynomialLogLaurentSolution_uniform_log_bound ν
      (fun k => (stage61_fourierLift A hf).coeff k.val) ξ hP s hs
    change HasUniformLogBound s (2*(sameFourierEulerCoefficientSymbols A hf 0).natDegree) at hb
    simpa only [sameFourierEulerIndicial_natDegree A hf hc] using hb
  · intro e rho p hrho hp i
    exact normalizedLaurentAmplitude_retained_fourier_index A hf hc e rho p hrho hp ξ s i

end StrictEUnit
end

#print axioms StrictEUnit.frobeniusIntegerShift_add
#print axioms StrictEUnit.normalizedLaurentAmplitude_retained_fourier_index
#print axioms StrictEUnit.fourierLaurentRealizationData
