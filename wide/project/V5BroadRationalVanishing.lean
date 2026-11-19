import V5BroadDivisionAtOne

noncomputable section
open scoped Topology
namespace StrictEUnit

/-- Division at one for actual rational-coefficient broad E-functions has no
conjugate-vanishing premise: every coefficient embedding fixes the same
rational coefficients, so the input to broad division already holds. -/
theorem v5_broad_rational_division_at_one (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex)
    (hf : Differentiable ℂ f)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic a)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hzero : f 1 = 0) :
    ∃ g : ℂ → ℂ, V5IsBroadEFunction g ∧ ∀ z, (1-z)*g z = f z := by
  apply v5_broad_division_at_one f a hf hs hODE ha
  intro σ
  have he (n : ℕ) : σ (a n) = (a n : ℂ) := by
    obtain ⟨q,hq⟩ := hrat n
    rw [hq, σ.commutes]
    exact ((algebraicClosure ℚ ℂ).val.commutes q).symm
  simpa only [he, one_pow, mul_one, hzero] using hs 1

/-- Rational-coefficient broad E-functions vanishing at one have a full
independent holomorphic solution family of the same minimal algebraic
equation, and all members vanish at one. The theorem concerns the original
function, not an equation for a separately selected function. -/
theorem v5_broad_rational_minimal_row_vanishing_at_one (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex)
    (hf : Differentiable ℂ f)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic a)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hzero : f 1 = 0) (hf0 : f ≠ 0)
    (m : ℕ) (p : ℕ → Polynomial AlgebraicComplex) (hp : p m ≠ 0)
    (hp0 : ∀ z, v5RowResidual f m p z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder AlgebraicComplex f l) :
    ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent 1 v ∧
      ∀ i, AnalyticAt ℂ (v i) 1 ∧ v i 1 = 0 ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (v i) m p z = 0 := by
  obtain ⟨g,hg,hgf⟩ := v5_broad_rational_division_at_one f a hf hs hODE ha hrat hzero
  have he : (fun z => (1-z)*g z) = f := funext hgf
  have hg0 : g ≠ 0 := by
    intro hz
    apply hf0
    rw [← he]
    funext z
    simp [hz]
  exact v5_actual_broad_affine_minimal_row_vanishing hg hg0 m p hp
    (he.symm ▸ hp0) (he.symm ▸ hmin)

#print axioms v5_broad_rational_division_at_one
#print axioms v5_broad_rational_minimal_row_vanishing_at_one
end StrictEUnit
end
