import StrictEArithmeticSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Algebraic scalar closure for full strict E-functions

Scalar multiplication and negation include their differential equations.
The addition and multiplication constructions below verify precisely the entire
series and arithmetic conditions, leaving general ODE closure separate.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A scalar multiple of an entire solution satisfies the same nonzero ODE. -/
theorem algebraicPolynomialODE_const_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hode : HasAlgebraicPolynomialODE f) (c : ℂ) :
    HasAlgebraicPolynomialODE (fun z => c * f z) := by
  obtain ⟨m, p, hp, heq⟩ := hode
  refine ⟨m, p, hp, ?_⟩
  intro z
  have hd (n : ℕ) : iteratedDeriv n (fun z => c * f z) z = c * iteratedDeriv n f z :=
    iteratedDeriv_const_mul hf.contDiff.contDiffAt c
  simp_rw [hd]
  calc
    _ = c * ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
        iteratedDeriv i.val f z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [heq z, mul_zero]

/-- Full strict E-function closure under algebraic scalar multiplication. -/
theorem strictEFunction_const_mul {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (α : AlgebraicComplex) :
    IsStrictEFunction (fun z => (α : ℂ) * f z) := by
  obtain ⟨a, hd, hs, ho, ha⟩ := hf
  refine ⟨(fun n => α * a n), (differentiable_const _).mul hd, ?_,
    algebraicPolynomialODE_const_mul hd ho (α : ℂ), strictEArithmetic_const_mul ha α⟩
  intro z
  exact strictE_egf_hasSum_const_mul (hs z) α

/-- Full strict E-function closure under negation. -/
theorem strictEFunction_neg {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    IsStrictEFunction (fun z => -f z) := by
  simpa using strictEFunction_const_mul hf (-1)

/-- Addition of full strict E-functions supplies every defining condition
except the separate general ODE-closure theorem. -/
theorem strictEFunction_add_analytic_arithmetic {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g) :
    ∃ a : ℕ → AlgebraicComplex,
      Differentiable ℂ (fun z => f z + g z) ∧
      (∀ z, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z + g z)) ∧
      HasStrictEArithmetic a := by
  obtain ⟨a, hdf, hsf, _, haf⟩ := hf
  obtain ⟨b, hdg, hsg, _, hag⟩ := hg
  exact ⟨(fun n => a n + b n), hdf.add hdg,
    (fun z => strictE_egf_hasSum_add (hsf z) (hsg z)), strictEArithmetic_add haf hag⟩

/-- Multiplication of full strict E-functions supplies every defining
condition except the separate general ODE-closure theorem. -/
theorem strictEFunction_mul_analytic_arithmetic {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g) :
    ∃ a : ℕ → AlgebraicComplex,
      Differentiable ℂ (fun z => f z * g z) ∧
      (∀ z, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z * g z)) ∧
      HasStrictEArithmetic a := by
  obtain ⟨a, hdf, hsf, _, haf⟩ := hf
  obtain ⟨b, hdg, hsg, _, hag⟩ := hg
  exact ⟨strictEBinomialConvolution a b, hdf.mul hdg,
    (fun z => strictE_egf_hasSum_mul haf hag (hsf z) (hsg z)),
    strictEArithmetic_binomialConvolution haf hag⟩

end StrictEUnit

#print axioms StrictEUnit.algebraicPolynomialODE_const_mul
#print axioms StrictEUnit.strictEFunction_const_mul
#print axioms StrictEUnit.strictEFunction_neg
#print axioms StrictEUnit.strictEFunction_add_analytic_arithmetic
#print axioms StrictEUnit.strictEFunction_mul_analytic_arithmetic
