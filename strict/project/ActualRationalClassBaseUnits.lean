import SelectedFourierRationalExponents
import ReindexedBlockDifferential
import RationalRamificationWeights

noncomputable section
open scoped Classical BigOperators
namespace StrictEUnit

/-- Rational class representatives, common ramification, and the actual
finite Laurent-log fundamental units for the retained Fourier blocks. -/
theorem actualFourier_rational_class_base_units {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      BinomialPrefixDenominators x) :
    let P := sameFourierEulerCoefficientSymbols A hf 0
    let b := fun k : Fin (nu+1) => (stage61_fourierLift A hf).coeff k.val
    let hP := sameFourierEulerIndicial_ne_zero A hf hc
    ∃ xi : ExponentClass rho → AlgebraicComplex, ∃ s : Fin nu → ℕ,
    ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) ≃ Fin nu,
      (∀ j, rho j = xi (exponentClassMap rho j) + (s j : AlgebraicComplex)) ∧
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : AlgebraicComplex)) ∧
      (∀ i, E i = e (naturalResonanceRootSeed P (xi i.1) hP i.2)) ∧
      ∃ N : ℕ, 0 < N ∧ ∃ m : ExponentClass rho → ℤ,
      (∀ c, (m c : AlgebraicComplex) / (N : AlgebraicComplex) = xi c) ∧
      ∀ c,
        let J := naturalResonanceLogMatrix nu b (xi c) hP
        let hJ := naturalResonanceLogMatrix_isNilpotent nu b (xi c) hP
        matrixDerivative (manuscriptBaseDerivation N) (fixedExponentBaseUnit (m c) J hJ).val =
          ramifiedConstantMatrix (Matrix.diagonal (fun _ : polynomialLogResonanceCoordinateIndex (xi c) (scalarEulerCoefficientSymbol nu (fun i k => PowerSeries.coeff AlgebraicComplex k (b i)) 0) => xi c) + J) *
            (fixedExponentBaseUnit (m c) J hJ).val := by
  dsimp only
  obtain ⟨xi,s,hs,hsep,E,hE,hcard⟩ := exists_disjoint_natural_resonance_equiv
    _ (sameFourierEulerIndicial_ne_zero A hf hc) e rho hrho
  have hr : ∀ j, ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = rho j := by
    intro j
    apply algebraicComplex_binomialPrefixDenominators_rational
    apply hroot
    rw [hrho j]
    exact frobeniusRootSeedExponent_isRoot _ (e.symm j)
  choose r hr using hr
  let q : ExponentClass rho → ℚ := fun c => r c.out - (s c.out : ℚ)
  have hq : ∀ c, (q c : AlgebraicComplex) = xi c := by
    intro c
    have hh := hs c.out
    have he : exponentClassMap rho c.out = c := Quotient.out_eq c
    rw [he, ← hr c.out] at hh
    dsimp [q]
    push_cast
    change algebraMap ℚ AlgebraicComplex (r c.out) - (s c.out : AlgebraicComplex) = xi c
    linear_combination hh
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  obtain ⟨N,hN,m,hm,heq⟩ := rational_weights_common_denominator_field (k := AlgebraicComplex) q
  have hm' : ∀ c, (m c : AlgebraicComplex) / (N : AlgebraicComplex) = xi c :=
    fun c => (hm c).trans (hq c)
  refine ⟨xi,s,E,hs,hsep,hE,N,hN,m,hm',?_⟩
  intro c
  exact fixedExponentBaseUnit_equation N hN.ne' (m c) (xi c) (hm' c) _ _

end StrictEUnit
end
