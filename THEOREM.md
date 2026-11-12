<!-- Modified for the source-focused edition, 12 November 2026. -->

# Theorem and definitions

Let $\mathcal E_{\mathrm{strict}}$ be the ring of values of strict E-functions at algebraic arguments. The classification is

$$
\mathcal E_{\mathrm{strict}}^\times
=\{\alpha\exp(\beta):\alpha\in\overline{\mathbb Q}^{\times},\ \beta\in\overline{\mathbb Q}\}.
$$

The authoritative statement is in [StrictEValueUnitClassification.lean](project/StrictEValueUnitClassification.lean), namespace `StrictEUnit`:

```lean
theorem strictEValueUnit_iff_algebraic_scalar_exp (u : ℂ) :
    IsStrictEValueUnit u ↔
      ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
        u = α * Complex.exp β :=
  strictEValueUnit_iff_algebraic_scalar_exp_of_arithmetic_inputs
    actualStrictE_commonArithmeticFrameAvailability strictELaurentRelationLifting u
```

Both arithmetic inputs are proved declarations. Neither is a remaining hypothesis of the endpoint. The numerical audit includes an explicitly typed example of the same equivalence. The source SHA-256 is `fc52dd6f442eeee2c3b24f1e44f8ebc7a503dabb2ae42a288e53cfd15c9bea51`; all proof sources are unchanged in this release.

## Definitions, verbatim from project source

These definitions are copied from [StrictEFunctionDefinitions.lean](project/StrictEFunctionDefinitions.lean), which supplies the imports and notation. `AlgebraicComplex` is the algebraic closure of ℚ inside ℂ.

```lean
abbrev AlgebraicComplex := algebraicClosure ℚ ℂ

def HasAlgebraicPolynomialODE (f : ℂ → ℂ) : Prop :=
  ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial AlgebraicComplex,
    (∃ i, p i ≠ 0) ∧
    ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val f z = 0

def HasStrictEArithmetic (a : ℕ → AlgebraicComplex) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    (∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n : ℕ, ‖σ (a n)‖ ≤ C ^ (n + 1)) ∧
    ∃ d : ℕ → ℕ, (∀ n, 0 < d n) ∧ (∀ n, (d n : ℝ) ≤ C ^ (n + 1)) ∧
      ∀ n j : ℕ, j ≤ n → IsIntegral ℤ ((d n : ℂ) * (a j : ℂ))

def IsStrictEFunction (f : ℂ → ℂ) : Prop :=
  ∃ a : ℕ → AlgebraicComplex,
    Differentiable ℂ f ∧
    (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) ∧
    HasAlgebraicPolynomialODE f ∧ HasStrictEArithmetic a

def IsStrictEValue (u : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, IsStrictEFunction f ∧ ∃ α : AlgebraicComplex, f α = u

def IsStrictEValueUnit (u : ℂ) : Prop :=
  u ≠ 0 ∧ IsStrictEValue u ∧ IsStrictEValue u⁻¹
```

Thus a strict E-function is entire, is represented everywhere by its factorial-normalized algebraic coefficient series, and satisfies a homogeneous linear ODE with algebraic polynomial coefficients not all zero. All coefficient conjugates and the common denominators of each initial segment have geometric bounds. A single finite coefficient field is subsequently derived from the ODE.

The unit predicate means exactly that a nonzero number and its reciprocal are both strict E-values. Ring closure is proved separately, and `strictEValueUnit_iff_exists_unit` identifies this predicate with the ordinary units of the value subring. Algebraic scalar exponentials and their reciprocal representations are constructed directly.

## Navigation and scope

| Purpose | Entry point |
| --- | --- |
| Mathematical construction and sensitive hypotheses | [PROOF.md](PROOF.md) |
| Exact source signatures, assumptions, dependencies and historical closures | [CONTRACTS.json](CONTRACTS.json) |
| Finite coefficient field and actual/formal correspondence | Contracts C02–C03 |
| Proved frame and relation-lifting inputs | Contracts C04–C06 |
| Exact fiber, character lifting and analytic unit classification | Contracts C07–C17 |
| Final assembly, reverse inclusion and ring units | Contracts C01, C18–C20 |
| Verification status and trust boundary | [VALIDATION.md](VALIDATION.md), [AUDIT.md](AUDIT.md) |
| Antecedents and contribution | [CITATION.md](CITATION.md) |

The endpoint addresses the **strict** class in Fischler–Rivoal's Conjecture 1.2. It does not replace the geometric bounds by Siegel's broader subfactorial conditions. No general recognition algorithm or separately formalized uniqueness theorem is claimed. Historical “unproved input” comments refer to intermediate conditional layers; the contract index names their later proofs.
