import AlgebraicComplexIndicialArithmetic
import SelectedRegularResidueArithmetic

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Either the ORIGINAL center is ordinary, or ALL actual algebraic roots of
the explicit SAME regular residue indicial polynomial have binomial common
prefix denominators. Rationality and Frobenius solutions are not asserted. -/
def SameClearingIndicialRootArithmeticData
    {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (φ : K →+* AlgebraicComplex) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let τ := t.coeff t.natTrailingDegree
  let β := polynomialCompanionFace n 1 1 t U
  (t.natTrailingDegree=0 ∧ t.coeff 0 ≠ 0) ∨
    (0<t.natTrailingDegree ∧ ∀ ξ : AlgebraicComplex,
      (regularResidueIndicial n (φ τ) (fun j => φ (β j))).eval ξ=0 →
      ∃ C : ℝ,1≤C ∧ ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(s+1) ∧
        ∀ m,m≤s → IsIntegral ℤ
          ((d:AlgebraicComplex)*((descPochhammer AlgebraicComplex m).eval ξ/(m.factorial:AlgebraicComplex))))

theorem selectedFuchsSourceData_all_indicial_root_arithmetic
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingIndicialRootArithmeticData n T UI φ := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  let t := T.map (algebraMap (𝓞 K) K)
  by_cases hzero : t.natTrailingDegree=0
  · exact Or.inl ⟨hzero,polynomial_zero_trailing_degree_ordinary t hT hzero⟩
  · have ht : 0<t.natTrailingDegree := Nat.pos_of_ne_zero hzero
    refine Or.inr ⟨ht,?_⟩
    intro ξ hξ
    exact same_clearing_algebraicComplex_indicial_binomial_denominators
      φ n c T UI hT hclear E hE hden ht ξ hξ

end StrictEUnit
end
