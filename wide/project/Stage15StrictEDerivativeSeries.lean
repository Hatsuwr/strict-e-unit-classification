import Stage15StrictEDerivativeArithmetic
import StrictETaylorRealization

/-!
# Actual differentiated strict E factorial series

The shifted series is the actual derivative at every complex point. The proof
uses uniqueness of the genuine Cauchy coefficients, their derivative formula,
and entire Cauchy reconstruction. No formal-to-analytic realization is assumed.
-/
noncomputable section
namespace StrictEUnit

/-- The actual factorial-series witness determines the genuine derivative
coefficients, with the factorial shift canceled exactly. -/
theorem strictE_egf_derivative_cauchyCoefficient {f : ℂ → ℂ}
    {a : ℕ → AlgebraicComplex} (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (n : ℕ) :
    entireCauchyCoefficient (deriv f) n = (a (n + 1) : ℂ) / (n.factorial : ℂ) := by
  have hc (j : ℕ) : entireCauchyCoefficient f j = (a j : ℂ) / (j.factorial : ℂ) := by
    apply entireCauchyCoefficient_eq_of_hasSum hf
    intro z
    convert hs z using 1
    funext k
    ring
  rw [entireCauchyCoefficient_deriv hf, hc, Nat.factorial_succ, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  push_cast
  push_cast at hn
  field_simp
  ring

/-- Entire Cauchy reconstruction proves the actual differentiated HasSum
identity at every z. This does not merely identify formal coefficients. -/
theorem strictE_egf_hasSum_derivative {f : ℂ → ℂ} {a : ℕ → AlgebraicComplex}
    (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (z : ℂ) :
    HasSum (fun n => (a (n + 1) : ℂ) * z ^ n / (n.factorial : ℂ)) (deriv f z) := by
  have hd : Differentiable ℂ (deriv f) :=
    differentiableOn_univ.mp (hf.differentiableOn.deriv isOpen_univ)
  convert entireCauchyCoefficient_hasSum hd z using 1
  funext n
  rw [strictE_egf_derivative_cauchyCoefficient hf hs]
  ring

end StrictEUnit
