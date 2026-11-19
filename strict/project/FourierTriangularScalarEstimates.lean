import FrobeniusScalarRatioBounds

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The actual lower-index scalar numerator uses rho+(n-k), exactly as in
the Frobenius convolution. Falling factorials are the normalization factors.
This is not yet an estimate of the full logarithmic differential inverse. -/
theorem sameFourier_eventually_factorial_scalar_ratio_bound
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) (φ : K →+* ℂ) (rho : K)
    (k : ℕ) (hk : k ≤ ν) :
    ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      ‖(((sameFourierEulerCoefficientSymbols A hf 0).map φ).eval (φ rho+(n : ℂ)))⁻¹‖ *
      ‖((sameFourierEulerCoefficientSymbols A hf k).map φ).eval (φ rho+((n-k : ℕ) : ℂ))‖ *
      (n.descFactorial k : ℝ) ≤ C := by
  let P := (sameFourierEulerCoefficientSymbols A hf 0).map φ
  let Q := (sameFourierEulerCoefficientSymbols A hf k).map φ
  have hP : P ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr
    (sameFourierEulerIndicial_ne_zero A hf hc)
  have hdegree : P.natDegree = ν := by
    simp only [P,Polynomial.natDegree_map_eq_of_injective φ.injective,sameFourierEulerIndicial_natDegree A hf hc]
  have hQ : Q.natDegree ≤ P.natDegree-k := by
    rw [hdegree]
    dsimp only [Q]
    rw [Polynomial.natDegree_map_eq_of_injective φ.injective]
    exact sameFourierEulerCoefficientSymbols_natDegree_le A hf k
  obtain ⟨N,C,hC,hbound⟩ := complexPolynomial_eventually_factorial_ratio_bound P Q hP
    (φ rho) (φ rho-(k : ℂ)) k (by rwa [hdegree]) hQ
  refine ⟨max N k,C,hC,?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnk : k ≤ n := (le_max_right _ _).trans hn
  have he : (φ rho-(k : ℂ))+(n : ℂ) = φ rho+((n-k : ℕ) : ℂ) := by
    rw [Nat.cast_sub hnk]
    ring
  simpa only [he,P,Q] using hbound n hnN

/-- Exact support and per-embedding scalar estimates for the SAME operator.
Constants may depend on the embedding, exponent and coefficient offset.
No uniform conjugate-growth or amplitude-growth conclusion is asserted. -/
def FourierTriangularEstimateData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,
  let B := sameFourierEulerCoefficientSymbols A hf
  (∀ n k,ν<n+k → (B n).coeff k = 0) ∧
  (∀ n,ν<n → B n = 0) ∧
  (∀ n,(B n).natDegree ≤ ν-n) ∧
  (∀ rho : K,∀ u : ℕ → Polynomial K,∀ n,
    polynomialLogEulerCoefficient B rho u n =
      ∑ s : Fin (n+1),if n-s.1 ≤ ν then
        shiftedPolynomialDifferentialOperator (rho+(s.1 : K)) (B (n-s.1)) (u s.1) else 0) ∧
  ∀ φ : K →+* ℂ,∀ rho : K,
    (∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      ((B 0).map φ).eval (φ rho+(n : ℂ)) ≠ 0 ∧
      ‖(((B 0).map φ).eval (φ rho+(n : ℂ)))⁻¹‖ ≤ C/((n : ℝ)+1)^ν) ∧
    ∀ k : ℕ,k≤ν → ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      ‖(((B 0).map φ).eval (φ rho+(n : ℂ)))⁻¹‖ *
      ‖((B k).map φ).eval (φ rho+((n-k : ℕ) : ℂ))‖ * (n.descFactorial k : ℝ) ≤ C

theorem fourierTriangularEstimateData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierTriangularEstimateData A := by
  intro hf
  dsimp only
  refine ⟨sameFourierEulerCoefficientSymbols_coeff_eq_zero_of_triangle A hf,
    sameFourierEulerCoefficientSymbols_eq_zero_above_order A hf,
    sameFourierEulerCoefficientSymbols_natDegree_le A hf,
    sameFourier_polynomialLogEulerCoefficient_finite_window A hf,?_⟩
  intro φ rho
  constructor
  · have hP := (Polynomial.map_ne_zero_iff φ.injective).mpr
      (sameFourierEulerIndicial_ne_zero A hf hc)
    simpa only [Polynomial.natDegree_map_eq_of_injective φ.injective,
      sameFourierEulerIndicial_natDegree A hf hc] using
      complexPolynomial_eventually_inverse_bound
        ((sameFourierEulerCoefficientSymbols A hf 0).map φ) hP (φ rho)
  · intro k hk
    exact sameFourier_eventually_factorial_scalar_ratio_bound A hf hc φ rho k hk

end StrictEUnit
end

#print axioms StrictEUnit.sameFourier_eventually_factorial_scalar_ratio_bound
#print axioms StrictEUnit.fourierTriangularEstimateData
