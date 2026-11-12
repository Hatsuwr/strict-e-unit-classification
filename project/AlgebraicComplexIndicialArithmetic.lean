import MappedIndicialBinomialArithmetic

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

/-- All actual algebraic roots are covered: no root-field containment or
rational-spectrum premise is imposed on the original selected input. -/
theorem same_clearing_algebraicComplex_indicial_binomial_denominators
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* AlgebraicComplex) (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K))=
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K))*
          minimalDerivativeCompanion (n+1) c i j)
    (E : ℝ) (hE : 1≤E)
    (hden : ∀ s : ℕ,∃ δ : ℕ,0<δ ∧ (δ:ℝ)≤E^(s+1) ∧
      ∀ m,m≤s → ∀ i j : Fin (n+1),∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) m i j).coeff l))
    (ht : 0<(T.map (algebraMap (𝓞 K) K)).natTrailingDegree)
    (ξ : AlgebraicComplex)
    (hξ : (regularResidueIndicial n
      (φ ((T.map (algebraMap (𝓞 K) K)).coeff (T.map (algebraMap (𝓞 K) K)).natTrailingDegree))
      (fun j => φ (polynomialCompanionFace n 1 1 (T.map (algebraMap (𝓞 K) K))
        (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) j))).eval ξ=0) :
    ∃ C : ℝ,1≤C ∧ ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(s+1) ∧
      ∀ m,m≤s → IsIntegral ℤ ((d:AlgebraicComplex)*((descPochhammer AlgebraicComplex m).eval ξ/(m.factorial:AlgebraicComplex))) := by
  letI : Algebra.IsAlgebraic ℤ AlgebraicComplex :=
    (IsFractionRing.comap_isAlgebraic_iff (A:=ℤ) (K:=ℚ) (C:=AlgebraicComplex)).mpr
      (inferInstance : Algebra.IsAlgebraic ℚ AlgebraicComplex)
  exact same_clearing_mapped_indicial_binomial_denominators
    φ n c T UI hT hclear E hE hden ht ξ hξ

end StrictEUnit
end
