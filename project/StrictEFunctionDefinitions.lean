import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import ExponentialGeneratingGrowth

/-!
# Strict E-functions and their numerical values

These predicates record the manuscript's actual analytic and arithmetic
conditions. They do not identify E-values with the proposed exponential class,
and no assertion that the E-values form a ring is built into their definition.
The ODE is recorded after clearing rational-function denominators, with
polynomial coefficients in the algebraic numbers and a genuinely nonzero
coefficient tuple.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The actual field of algebraic numbers inside the complex numbers. -/
abbrev AlgebraicComplex := algebraicClosure ℚ ℂ

/-- The denominator-cleared nonzero homogeneous linear differential equation.
The index is the derivative order, and the coefficients are actual polynomials
over the algebraic numbers. -/
def HasAlgebraicPolynomialODE (f : ℂ → ℂ) : Prop :=
  ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial AlgebraicComplex,
    (∃ i, p i ≠ 0) ∧
    ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val f z = 0

/-- Geometric bounds at every algebraic embedding, and positive integer common
denominators for every initial coefficient segment, with the same constant. -/
def HasStrictEArithmetic (a : ℕ → AlgebraicComplex) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    (∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n : ℕ, ‖σ (a n)‖ ≤ C ^ (n + 1)) ∧
    ∃ d : ℕ → ℕ, (∀ n, 0 < d n) ∧ (∀ n, (d n : ℝ) ≤ C ^ (n + 1)) ∧
      ∀ n j : ℕ, j ≤ n → IsIntegral ℤ ((d n : ℂ) * (a j : ℂ))

/-- A strict E-function is an entire function represented by its actual
factorial-normalized algebraic series, satisfying the nonzero algebraic ODE
and both conjugate and denominator conditions. -/
def IsStrictEFunction (f : ℂ → ℂ) : Prop :=
  ∃ a : ℕ → AlgebraicComplex,
    Differentiable ℂ f ∧
    (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) ∧
    HasAlgebraicPolynomialODE f ∧ HasStrictEArithmetic a

/-- Strict E-values use algebraic arguments, not arbitrary complex arguments.
Normalization to the argument one is a theorem to be proved, not a definition. -/
def IsStrictEValue (u : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, IsStrictEFunction f ∧ ∃ α : AlgebraicComplex, f α = u

/-- Numerical unit membership, without presupposing unproved ring closure.
When the strict E-values have been proved to form a subring, this is precisely
the underlying membership criterion for a unit of that subring. -/
def IsStrictEValueUnit (u : ℂ) : Prop :=
  u ≠ 0 ∧ IsStrictEValue u ∧ IsStrictEValue u⁻¹

/-- The full embedding condition includes the chosen complex embedding. -/
theorem strictEArithmetic_chosen_bound {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, ‖(a n : ℂ)‖ ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hconj, _⟩ := ha
  exact ⟨C, hC, hconj (algebraicClosure ℚ ℂ).val⟩

/-- Every strict E-function has the exact exponential-type bound, now derived
from its full definition and its actual factorial-normalized series. -/
theorem strictEFunction_exponential_bound {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖) := by
  obtain ⟨a, _, hs, _, ha⟩ := hf
  obtain ⟨C, hC, hbound⟩ := strictEArithmetic_chosen_bound ha
  exact ⟨C, hC, function_norm_le_of_geometric_egf (fun n => (a n : ℂ)) C hbound f hs⟩

/-- The actual coefficients can be recovered at the origin; in particular,
a transcendental constant cannot pass as an algebraic constant coefficient. -/
theorem strictEFunction_zero_isAlgebraic {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    IsAlgebraic ℚ (f 0) := by
  obtain ⟨a, _, hs, _, _⟩ := hf
  have hzero : f 0 = (a 0 : ℂ) := by
    rw [← (hs 0).tsum_eq, tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  rw [hzero]
  exact (mem_algebraicClosure_iff.mp (a 0).property)

set_option synthInstance.maxHeartbeats 20000 in
/-- Extending an embedding of a subfield into the algebraically closed complex
field proves that the conjugate bound really applies in every number field
inside the algebraic numbers. No finiteness restriction is needed. -/
theorem algebraicComplex_embedding_extends (K : IntermediateField ℚ AlgebraicComplex)
    (σ : K →ₐ[ℚ] ℂ) :
    ∃ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ x : K, τ (x : AlgebraicComplex) = σ x := by
  letI : Module ℚ K := Algebra.toModule
  letI : Algebra.IsAlgebraic K AlgebraicComplex := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  obtain ⟨τ, hτ⟩ :=
    IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ) (L := K) (E := AlgebraicComplex) (M := ℂ) σ
  exact ⟨τ, fun x => DFunLike.congr_fun hτ x⟩

/-- Consequently the arithmetic bound includes every image under every
embedding of any number field containing the coefficient. -/
theorem strictEArithmetic_numberField_conjugates {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : IntermediateField ℚ AlgebraicComplex)
      (σ : K →ₐ[ℚ] ℂ) (n : ℕ) (x : K), (x : AlgebraicComplex) = a n →
      ‖σ x‖ ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hbound, _⟩ := ha
  refine ⟨C, hC, ?_⟩
  intro K σ n x hx
  obtain ⟨τ, hτ⟩ := algebraicComplex_embedding_extends K σ
  rw [← hτ x, hx]
  exact hbound τ n

end StrictEUnit
#print axioms StrictEUnit.HasAlgebraicPolynomialODE
#print axioms StrictEUnit.HasStrictEArithmetic
#print axioms StrictEUnit.IsStrictEFunction
#print axioms StrictEUnit.IsStrictEValue
#print axioms StrictEUnit.IsStrictEValueUnit
#print axioms StrictEUnit.strictEArithmetic_chosen_bound
#print axioms StrictEUnit.strictEFunction_exponential_bound
#print axioms StrictEUnit.strictEFunction_zero_isAlgebraic
#print axioms StrictEUnit.algebraicComplex_embedding_extends
#print axioms StrictEUnit.strictEArithmetic_numberField_conjugates

#print axioms StrictEUnit.AlgebraicComplex
