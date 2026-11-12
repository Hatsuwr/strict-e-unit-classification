import RegularResidueArithmetic
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- The ORIGINAL clearing is either ordinary at zero, or its derived regular
residue has the literal falling-product identity and common-prefix binomial
arithmetic. Positive trailing order is a branch conclusion, never an input. -/
def SameClearingRegularResidueArithmeticData
    {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let τ := t.coeff t.natTrailingDegree
  let β := polynomialCompanionFace n 1 1 t U
  let v := T.coeff t.natTrailingDegree
  let q := Int.natAbs (Algebra.norm ℤ v)
  (t.natTrailingDegree=0 ∧ t.coeff 0 ≠ 0) ∨
    (0<t.natTrailingDegree ∧
      (∀ m,polynomialConnectionFaceRow n 1 1 t U m=
        τ^m • ((Pi.single 0 1) ᵥ* matrixFallingProduct (regularCompanionResidue n τ β) m)) ∧
      0<q ∧ 1 ≤ (q:ℝ)*E ∧ ∀ s : ℕ,∃ d : ℕ,
        0<d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
        ∀ m,m≤s → ∀ j : Fin (n+1),
          IsIntegral ℤ ((d:K)*regularResidueBinomialRow n τ β m j))

theorem same_integral_clearing_regular_residue_alternative
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K))=
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K))*
          minimalDerivativeCompanion (n+1) c i j)
    (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ,∃ δ : ℕ,0<δ ∧ (δ:ℝ) ≤ E^(s+1) ∧
      ∀ m,m≤s → ∀ i j : Fin (n+1),∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) m i j).coeff l)) :
    SameClearingRegularResidueArithmeticData n T UI E := by
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  by_cases hzero : t.natTrailingDegree=0
  · exact Or.inl ⟨hzero,polynomial_zero_trailing_degree_ordinary t hT hzero⟩
  · have ht : 0<t.natTrailingDegree := Nat.pos_of_ne_zero hzero
    have hV := companion_common_denominators_local_bounds n c t U hT hclear E hE hden
    exact Or.inr ⟨ht,polynomialConnectionFaceRow_eq_residue_falling_product
      n c t U hT hclear ht hV,same_integral_clearing_regular_residue_denominators
        n c T UI hT hclear E hE hden ht⟩

/-- The full selected source packet itself discharges all arithmetic and
regularity inputs. No positive-order, spectrum or solution-family premise. -/
theorem selectedFuchsSourceData_regular_residue_arithmetic
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingRegularResidueArithmeticData n T UI E := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  exact same_integral_clearing_regular_residue_alternative n c T UI hT hclear E hE hden

end StrictEUnit
end
