import FrobeniusTriangularRecurrenceMajorant
import Mathlib.Analysis.SpecificLimits.Normed

/-! Genuine factorial-normalized bounds and absolute convergence for the exact
Fourier amplitudes, separately at each complex embedding. This does not assert
exponential arithmetic denominators or uniformity over all embeddings. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem sameFourier_factorial_coefficient_bound
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) (φ : K →+* ℂ) (rho : K) (u0 : Polynomial K) :
    ∃ C : ℝ,1≤C ∧ ∀ n j : ℕ,
      (n.factorial : ℝ)*‖φ ((polynomialLogFrobeniusCoefficient
        (sameFourierEulerCoefficientSymbols A hf) rho u0 n).coeff j)‖ ≤ C^(n+1) := by
  let B := sameFourierEulerCoefficientSymbols A hf
  let BC := fun k => (B k).map φ
  have hP : BC 0 ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr
    (sameFourierEulerIndicial_ne_zero A hf hc)
  have hdegree : (BC 0).natDegree = ν := by
    simp only [BC,B,Polynomial.natDegree_map_eq_of_injective φ.injective,sameFourierEulerIndicial_natDegree A hf hc]
  have hzero : ∀ k,ν<k → BC k=0 := by
    intro k hk
    simp only [BC,B,sameFourierEulerCoefficientSymbols_eq_zero_above_order A hf k hk,Polynomial.map_zero]
  have hdeg : ∀ k,(BC k).natDegree ≤ ν-k := by
    intro k
    simpa only [BC,Polynomial.natDegree_map_eq_of_injective φ.injective] using
      sameFourierEulerCoefficientSymbols_natDegree_le A hf k
  obtain ⟨C,hC,hbound⟩ := triangularFrobenius_factorial_geometric_bound BC (φ rho) (u0.map φ) ν hP hdegree hzero hdeg
  refine ⟨C,hC,?_⟩
  intro n j
  have hd := polynomialLogFrobeniusCoefficient_uniform_degree BC (φ rho) (u0.map φ) n
  rw [hdegree] at hd
  have hcoeff := polynomialLogSize_coeff_le ((u0.map φ).natDegree+ν)
    (polynomialLogFrobeniusCoefficient BC (φ rho) (u0.map φ) n) j hd
  rw [← polynomialLogFrobeniusCoefficient_map φ B rho u0 n,Polynomial.coeff_map] at hcoeff
  have hb := hbound n
  rw [← polynomialLogFrobeniusCoefficient_map φ B rho u0 n] at hb
  exact (mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)).trans hb

/-- Factorial-normalized bounds imply absolute convergence at EVERY complex
argument. This is a series theorem, not identification with a singular germ. -/
theorem factorial_geometric_absolutely_summable (a : ℕ → ℂ) (C : ℝ) (hC : 1≤C)
    (h : ∀ n,(n.factorial : ℝ)*‖a n‖ ≤ C^(n+1)) (z : ℂ) :
    Summable (fun n : ℕ => ‖a n*z^n‖) := by
  have hC0 : 0≤C := le_trans (by norm_num) hC
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (f := fun n : ℕ => C*((C*‖z‖)^n/(n.factorial : ℝ)))
  · intro n
    have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have ha : ‖a n‖ ≤ C^(n+1)/(n.factorial : ℝ) :=
      (le_div_iff₀ hf).mpr (by simpa only [mul_comm] using h n)
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (C^(n+1)/(n.factorial : ℝ))*‖z‖^n :=
        mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) _)
      _ = _ := by rw [pow_succ,mul_pow]; ring
  · exact (Real.summable_pow_div_factorial (C*‖z‖)).mul_left C

theorem sameFourier_amplitude_factorial_bound
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) (φ : K →+* ℂ) (rho : K) (u0 : Polynomial K) :
    ∃ C : ℝ,1≤C ∧ ∀ n j : ℕ,
      (n.factorial : ℝ)*‖φ (((polynomialLogFrobeniusAmplitude
        (sameFourierEulerCoefficientSymbols A hf) rho u0).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1) := by
  simpa only [polynomialLogFrobeniusAmplitude_coeff] using
    sameFourier_factorial_coefficient_bound A hf hc φ rho u0

def FourierAmplitudeGeometricGrowthData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,∀ φ : K →+* ℂ,∀ rho : K,∀ u0 : Polynomial K,
    (∃ C : ℝ,1≤C ∧ ∀ n j : ℕ,
      (n.factorial : ℝ)*‖φ (((polynomialLogFrobeniusAmplitude
        (sameFourierEulerCoefficientSymbols A hf) rho u0).coeff j).coeff (n : ℤ))‖ ≤ C^(n+1)) ∧
    ∀ j : ℕ,∀ z : ℂ,Summable (fun n : ℕ =>
      ‖φ (((polynomialLogFrobeniusAmplitude
        (sameFourierEulerCoefficientSymbols A hf) rho u0).coeff j).coeff (n : ℤ))*z^n‖)

theorem fourierAmplitudeGeometricGrowthData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierAmplitudeGeometricGrowthData A := by
  intro hf φ rho u0
  obtain ⟨C,hC,hbound⟩ := sameFourier_amplitude_factorial_bound A hf hc φ rho u0
  refine ⟨⟨C,hC,hbound⟩,?_⟩
  intro j z
  exact factorial_geometric_absolutely_summable _ C hC (fun n => hbound n j) z

end StrictEUnit
end
