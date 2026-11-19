# Theorem and definitions

Let $\mathcal E_{\mathrm{broad}}$ be the ring of values of broad Siegel E-functions at algebraic arguments. The classification is

$$
\mathcal E_{\mathrm{broad}}^\times
=\{\alpha\exp(\beta):\alpha\in\overline{\mathbb Q}^{\times},\ \beta\in\overline{\mathbb Q}\}.
$$

The authoritative declaration is in `V5WideFinal140.lean`, namespace `StrictEUnit`:

```lean
theorem v5_wide_unit_classification140 (u : ℂ) :
    V5IsWideEValueUnit131 u ↔
      ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
        u = α * Complex.exp β
```

There are no extra mathematical hypotheses. The Lean endpoint uses the numerical unit predicate rather than a bundled subring type. Its proof handles arbitrary algebraic evaluation arguments by rescaling to one.

## Definitions, verbatim from project source

`AlgebraicComplex` is the algebraic closure of ℚ inside ℂ. `HasAlgebraicPolynomialODE` is the original strict edition's predicate for a nontrivial homogeneous linear ODE over algebraic polynomial coefficients.

From `V5BroadAlgebraicDescent.lean` and `V5BroadActualData.lean`:

```lean
def V5BroadAlgebraicArithmetic (a : ℕ → AlgebraicComplex) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℕ → ℕ, (∀ L, 0 < δ L) ∧
      (∀ L, (δ L : ℝ) ≤ C^(L+1) * (L.factorial : ℝ)^ε) ∧
      (∀ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n,
        ‖τ (a n)‖ ≤ C^(n+1) * (n.factorial : ℝ)^ε) ∧
      (∀ L n, n ≤ L → IsIntegral ℤ ((δ L : ℂ) * (a n : ℂ)))

def V5IsBroadEFunction (f : ℂ → ℂ) : Prop :=
  ∃ a : ℕ → AlgebraicComplex,
    Differentiable ℂ f ∧
    (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) ∧
    HasAlgebraicPolynomialODE f ∧ V5BroadAlgebraicArithmetic a
```

From `V5WideValueClassificationBoundary131.lean`:

```lean
def V5IsWideEValue131 (u : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, V5IsBroadEFunction f ∧ ∃ a : AlgebraicComplex, f a = u

def V5IsWideEValueUnit131 (u : ℂ) : Prop :=
  u ≠ 0 ∧ V5IsWideEValue131 u ∧ V5IsWideEValue131 u⁻¹
```

The bounds apply to all coefficient conjugates and to a single positive integer clearing each initial segment. They are equivalent to the conventional subfactorial bounds: to remove the factor $C^{n+1}$, use the Lean bound with exponent $\varepsilon/2$ and absorb this geometric factor into a constant times $(n!)^{\varepsilon/2}$. Least positive common denominators may be used to make the choice independent of the exponent. The polynomial ODE is the rational ODE with denominators cleared; the proof derives a common number field for the coefficients from the equation.

See [PROOF-v5.md](PROOF-v5.md) for the construction. The earlier [strict endpoint and definitions](https://github.com/Hatsuwr/strict-e-unit-classification/blob/340c7435608e0f1aa1d9b08a0100721a4fd23005/THEOREM.md) are unchanged at their original commit.
