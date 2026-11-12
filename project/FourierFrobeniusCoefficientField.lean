import FrobeniusRecurrenceFieldDescent
import FourierIntegerResonanceBasis

/-! One finite number field contains every coefficient of the exact finite
Fourier Frobenius family. This is field descent, not strict-E growth. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem sameFourierEulerCoefficientSymbols_mem_field
    (F : IntermediateField ℚ AlgebraicComplex) {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hA : ∀ i j,A i j ∈ F)
    (hdesc : ∀ (i : Fin (μ+1)) (j : Fin (ν+1)) k,
      (stage61_shiftedDesc (K := AlgebraicComplex) i.1 j.1).coeff k ∈ F)
    (n k : ℕ) : (sameFourierEulerCoefficientSymbols A hf n).coeff k ∈ F := by
  have hb (ell : ℕ) : PowerSeries.coeff AlgebraicComplex n
      ((stage61_fourierLift A hf).coeff ell) ∈ F := by
    have h := congrArg (fun s : LaurentSeries AlgebraicComplex => s.coeff (n : ℤ))
      (stage59_regularLift_map_coeff (stage61_fourierEulerSymbol A)
        (stage61_fourierEulerSymbol_regular A hf) ell)
    change (((stage61_fourierLift A hf).coeff ell : PowerSeries AlgebraicComplex) :
      LaurentSeries AlgebraicComplex).coeff (n : ℤ) = _ at h
    rw [LaurentSeries.coeff_coe_powerSeries] at h
    rw [h,stage61_fourierEulerSymbol_coeff]
    simp only [HahnSeries.coeff_sum]
    apply F.sum_mem
    intro i hi
    apply F.sum_mem
    intro j hj
    rw [HahnSeries.coeff_single]
    split_ifs
    · exact F.mul_mem (F.mul_mem (pow_mem (F.neg_mem F.one_mem) _) (hA i j)) (hdesc i j ell)
    · exact F.zero_mem
  unfold sameFourierEulerCoefficientSymbols scalarEulerCoefficientSymbol
  rw [Polynomial.finset_sum_coeff]
  apply F.sum_mem
  intro i hi
  rw [Polynomial.coeff_monomial]
  split_ifs
  · exact hb i.1
  · exact F.zero_mem

/-- Finite source data and exponents determine ONE finite field for ALL
recurrence and Laurent/log coefficients, uniformly across the entire family. -/
theorem finite_fourierFrobenius_coefficient_field
    {ι : Type*} [Fintype ι] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (rho : ι → AlgebraicComplex) (seed : ι → ℕ)
    (F : IntermediateField ℚ AlgebraicComplex) (hF : FiniteDimensional ℚ F) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F ≤ E ∧
      (∀ i j,A i j ∈ E) ∧ (∀ i,rho i ∈ E) ∧
      (∀ n j,(sameFourierEulerCoefficientSymbols A hf n).coeff j ∈ E) ∧
      (∀ i n j,(polynomialLogFrobeniusCoefficient (sameFourierEulerCoefficientSymbols A hf)
        (rho i) (Polynomial.X^seed i) n).coeff j ∈ E) ∧
      ∀ i j n,((polynomialLogFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf)
        (rho i) (Polynomial.X^seed i)).coeff j).coeff n ∈ E := by
  let data : ((Fin (μ+1) × Fin (ν+1)) ⊕ ((Fin (μ+1) × Fin (ν+1)) ⊕ ι)) →
      Polynomial AlgebraicComplex := fun i => match i with
    | Sum.inl ij => Polynomial.C (A ij.1 ij.2)
    | Sum.inr (Sum.inl ij) => stage61_shiftedDesc ij.1.1 ij.2.1
    | Sum.inr (Sum.inr j) => Polynomial.C (rho j)
  obtain ⟨E,hE,hFE,hdata⟩ := stage26_finite_coefficient_field_enlarge_polynomials F hF data
  have hA : ∀ i j,A i j ∈ E := by
    intro i j
    simpa only [data,Polynomial.coeff_C_zero] using hdata (Sum.inl (i,j)) 0
  have hrho : ∀ i,rho i ∈ E := by
    intro i
    simpa only [data,Polynomial.coeff_C_zero] using hdata (Sum.inr (Sum.inr i)) 0
  have hdesc : ∀ (i : Fin (μ+1)) (j : Fin (ν+1)) k,
      (stage61_shiftedDesc (K := AlgebraicComplex) i.1 j.1).coeff k ∈ E := by
    intro i j k
    exact hdata (Sum.inr (Sum.inl (i,j))) k
  have hB := sameFourierEulerCoefficientSymbols_mem_field E A hf hA hdesc
  have hseed (i : ι) (j : ℕ) : (Polynomial.X^seed i : Polynomial AlgebraicComplex).coeff j ∈ E := by
    rw [Polynomial.coeff_X_pow]
    split_ifs
    · exact E.one_mem
    · exact E.zero_mem
  refine ⟨E,hE,hFE,hA,hrho,hB,?_,?_⟩
  · intro i n j
    exact polynomialLogFrobeniusCoefficient_mem_field E _ (rho i) _ hB (hrho i) (hseed i) n j
  · intro i j n
    exact polynomialLogFrobeniusAmplitude_mem_field E _ (rho i) _ hB (hrho i) (hseed i) j n

/-- Apply descent to every exact retained indexing of the constructed family.
No new amplitudes or exponents replace those witnesses. -/
def FourierAmplitudeCoefficientFieldData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) : Prop :=
  ∀ F : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ F →
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ rho : Fin ν → AlgebraicComplex,∀ p : Fin ν → Polynomial (LaurentSeries AlgebraicComplex),
    (∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F ≤ E ∧
      (∀ i j,A i j ∈ E) ∧ (∀ i,rho i ∈ E) ∧
      (∀ n j,(sameFourierEulerCoefficientSymbols A hf n).coeff j ∈ E) ∧
      ∀ i j n,((p i).coeff j).coeff n ∈ E

theorem fourierAmplitudeCoefficientFieldData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) :
    FourierAmplitudeCoefficientFieldData A := by
  intro F hF hf e rho p hrho hp
  obtain ⟨E,hE,hFE,hA,hr,hB,hcoeff,hamp⟩ := finite_fourierFrobenius_coefficient_field A hf rho
    (fun i => frobeniusRootSeedOrder _ (e.symm i)) F hF
  refine ⟨E,hE,hFE,hA,hr,hB,?_⟩
  intro i j n
  rw [hp]
  change ((polynomialLogFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf)
    (frobeniusRootSeedExponent _ (e.symm i)) (Polynomial.X^frobeniusRootSeedOrder _ (e.symm i))).coeff j).coeff n ∈ E
  rw [← hrho]
  exact hamp i j n

end StrictEUnit
end

#print axioms StrictEUnit.sameFourierEulerCoefficientSymbols_mem_field
#print axioms StrictEUnit.finite_fourierFrobenius_coefficient_field
#print axioms StrictEUnit.fourierAmplitudeCoefficientFieldData
