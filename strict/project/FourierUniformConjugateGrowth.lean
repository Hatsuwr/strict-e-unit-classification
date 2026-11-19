import FiniteFieldUniformConjugateBounds

/-! ONE geometric constant for all conjugates of the exact finite Fourier
amplitude family. This proves the conjugate-growth half of strict-E arithmetic
for the literal factorial-normalized coefficients. Denominators remain separate. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- Literal coefficients for the factorial-series convention, with no change
to the underlying amplitude or to its logarithmic index. -/
def logAmplitudeFactorialCoefficient (p : Polynomial (LaurentSeries AlgebraicComplex))
    (j n : ℕ) : AlgebraicComplex :=
  (n.factorial : AlgebraicComplex)*((p.coeff j).coeff (n : ℤ))

theorem logAmplitudeFactorialCoefficient_mem
    (E : IntermediateField ℚ AlgebraicComplex)
    (p : Polynomial (LaurentSeries AlgebraicComplex)) (j n : ℕ)
    (h : (p.coeff j).coeff (n : ℤ) ∈ E) : logAmplitudeFactorialCoefficient p j n ∈ E :=
  E.mul_mem (E.natCast_mem _) h

theorem logAmplitudeFactorialCoefficient_norm
    (φ : AlgebraicComplex →+* ℂ)
    (p : Polynomial (LaurentSeries AlgebraicComplex)) (j n : ℕ) :
    ‖φ (logAmplitudeFactorialCoefficient p j n)‖ =
      (n.factorial : ℝ)*‖φ ((p.coeff j).coeff (n : ℤ))‖ := by
  simp only [logAmplitudeFactorialCoefficient,map_mul,map_natCast,norm_mul,Complex.norm_natCast]

/-- Normalization preserves the actual term of the convergent series. -/
theorem logAmplitudeFactorialCoefficient_series_term
    (φ : AlgebraicComplex →+* ℂ)
    (p : Polynomial (LaurentSeries AlgebraicComplex)) (j n : ℕ) (z : ℂ) :
    φ (logAmplitudeFactorialCoefficient p j n)*z^n/(n.factorial : ℂ) =
      φ ((p.coeff j).coeff (n : ℤ))*z^n := by
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [logAmplitudeFactorialCoefficient,map_mul,map_natCast]
  field_simp
  ring

/-- Field descent and per-embedding estimates combine into a SINGLE bound
uniform over all conjugates, family members, log degrees and natural indices. -/
theorem sameFourier_retained_uniform_conjugate_bound
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (F : IntermediateField ℚ AlgebraicComplex) (hF : FiniteDimensional ℚ F)
    (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → AlgebraicComplex) (p : Fin ν → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i = frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i = sameFourierTwistedAmplitude A hf (e.symm i)) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      (∀ i j,A i j ∈ E) ∧ (∀ i,rho i ∈ E) ∧
      (∀ n j,(sameFourierEulerCoefficientSymbols A hf n).coeff j ∈ E) ∧
      (∀ i j n,((p i).coeff j).coeff n ∈ E) ∧
      (∀ i j n,logAmplitudeFactorialCoefficient (p i) j n ∈ E) ∧
      ∃ C : ℝ,1≤C ∧
        (∀ (φ : AlgebraicComplex →+* ℂ) (i : Fin ν) (j n : ℕ),
          (n.factorial : ℝ)*‖φ (((p i).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1)) ∧
        ∀ (σ : AlgebraicComplex →ₐ[ℚ] ℂ) (i : Fin ν) (j n : ℕ),
          ‖σ (logAmplitudeFactorialCoefficient (p i) j n)‖ ≤ C^(n+1) := by
  obtain ⟨E,hE,hFE,hA,hr,hB,hamp⟩ :=
    fourierAmplitudeCoefficientFieldData A F hF hf e rho p hrho hp
  have hnormmem : ∀ i j n,logAmplitudeFactorialCoefficient (p i) j n ∈ E := by
    intro i j n
    exact logAmplitudeFactorialCoefficient_mem E (p i) j n (hamp i j (n : ℤ))
  have hbounds : ∀ φ : AlgebraicComplex →+* ℂ,∃ C : ℝ,1≤C ∧
      ∀ (ij : Fin ν × ℕ) (n : ℕ),(n.factorial : ℝ)*‖φ (((p ij.1).coeff ij.2).coeff (n : ℤ))‖ ≤ C^(n+1) := by
    intro φ
    obtain ⟨C,hC,hbound⟩ := sameFourier_retained_family_factorial_bound A hf hc e p hp φ
    exact ⟨C,hC,fun ij n => hbound ij.1 ij.2 n⟩
  obtain ⟨C,hC,hbound⟩ := finite_field_uniform_weighted_geometric_bound E hE
    (fun (ij : Fin ν × ℕ) n => ((p ij.1).coeff ij.2).coeff (n : ℤ))
    (fun ij n => hamp ij.1 ij.2 (n : ℤ)) (fun n => (n.factorial : ℝ)) hbounds
  refine ⟨E,hE,hFE,hA,hr,hB,hamp,hnormmem,C,hC,?_,?_⟩
  · intro φ i j n
    exact hbound φ (i,j) n
  · intro σ i j n
    exact (logAmplitudeFactorialCoefficient_norm σ.toRingHom (p i) j n).trans_le
      (hbound σ.toRingHom (i,j) n)

/-- No new growth or number-field assumption is added to the selected family.
The field can enlarge any specified finite source field. -/
def FourierUniformConjugateGrowthData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) : Prop :=
  ∀ F : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ F →
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ rho : Fin ν → AlgebraicComplex,∀ p : Fin ν → Polynomial (LaurentSeries AlgebraicComplex),
    (∀ i,rho i = frobeniusRootSeedExponent _ (e.symm i)) →
    (∀ i,p i = sameFourierTwistedAmplitude A hf (e.symm i)) →
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      (∀ i j,A i j ∈ E) ∧ (∀ i,rho i ∈ E) ∧
      (∀ n j,(sameFourierEulerCoefficientSymbols A hf n).coeff j ∈ E) ∧
      (∀ i j n,((p i).coeff j).coeff n ∈ E) ∧
      (∀ i j n,logAmplitudeFactorialCoefficient (p i) j n ∈ E) ∧
      ∃ C : ℝ,1≤C ∧
        (∀ (φ : AlgebraicComplex →+* ℂ) (i : Fin ν) (j n : ℕ),
          (n.factorial : ℝ)*‖φ (((p i).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1)) ∧
        ∀ (σ : AlgebraicComplex →ₐ[ℚ] ℂ) (i : Fin ν) (j n : ℕ),
          ‖σ (logAmplitudeFactorialCoefficient (p i) j n)‖ ≤ C^(n+1)

theorem fourierUniformConjugateGrowthData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) : FourierUniformConjugateGrowthData A :=
  sameFourier_retained_uniform_conjugate_bound A hc

end StrictEUnit
end
