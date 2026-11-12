import FourierAmplitudeGeometricGrowth

/-! The checked bounds apply to the SAME retained finite family. A single
constant controls every family member, log degree and index at each embedding. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem sameFourier_retained_family_factorial_bound
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (p : Fin ν → Polynomial (LaurentSeries K))
    (hp : ∀ i,p i = sameFourierTwistedAmplitude A hf (e.symm i)) (φ : K →+* ℂ) :
    ∃ C : ℝ,1≤C ∧ ∀ (i : Fin ν) (j n : ℕ),
      (n.factorial : ℝ)*‖φ (((p i).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1) := by
  have h : ∀ i : Fin ν,∃ C : ℝ,1≤C ∧ ∀ n j : ℕ,
      (n.factorial : ℝ)*‖φ (((p i).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1) := by
    intro i
    rw [hp i]
    exact sameFourier_amplitude_factorial_bound A hf hc φ _ _
  choose C hC hb using h
  let M : ℝ := 1+∑ i : Fin ν,C i
  have hsum : 0≤∑ i : Fin ν,C i := Finset.sum_nonneg (fun i hi => le_trans (by norm_num) (hC i))
  have hM : 1≤M := by dsimp only [M]; linarith
  refine ⟨M,hM,?_⟩
  intro i j n
  have hsingle : C i ≤ ∑ k : Fin ν,C k :=
    Finset.single_le_sum (fun k hk => le_trans (by norm_num) (hC k)) (Finset.mem_univ i)
  have hle : C i ≤ M := by dsimp only [M]; linarith
  exact (hb i n j).trans (pow_le_pow_left₀ (le_trans (by norm_num) (hC i)) hle (n+1))

def FourierRetainedAmplitudeGrowthData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  FourierAmplitudeGeometricGrowthData A ∧
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ p : Fin ν → Polynomial (LaurentSeries K),
    (∀ i,p i = sameFourierTwistedAmplitude A hf (e.symm i)) →
    ∀ φ : K →+* ℂ,
      (∃ C : ℝ,1≤C ∧ ∀ (i : Fin ν) (j n : ℕ),
        (n.factorial : ℝ)*‖φ (((p i).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1)) ∧
      ∀ (i : Fin ν) (j : ℕ) (z : ℂ),
        Summable (fun n : ℕ => ‖φ (((p i).coeff j).coeff (n : ℤ))*z^n‖)

theorem fourierRetainedAmplitudeGrowthData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierRetainedAmplitudeGrowthData A := by
  refine ⟨fourierAmplitudeGeometricGrowthData A hc,?_⟩
  intro hf e p hp φ
  obtain ⟨C,hC,hbound⟩ := sameFourier_retained_family_factorial_bound A hf hc e p hp φ
  refine ⟨⟨C,hC,hbound⟩,?_⟩
  intro i j z
  exact factorial_geometric_absolutely_summable _ C hC (fun n => hbound i j n) z

end StrictEUnit
end
