import V5BroadActualProduct
import V5BroadFactorialShiftArithmetic
import Stage15StrictEDerivativeClosure

/-! Actual derivatives of wide E-functions retain the exact shifted factorial
series, arbitrary-epsilon arithmetic and a nonzero algebraic polynomial ODE. -/
noncomputable section
namespace StrictEUnit

theorem v5_broad_actual_deriv_hasAlgebraicPolynomialODE {f : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) : HasAlgebraicPolynomialODE (deriv f) := by
  obtain ⟨a, hd, hs, ho, _⟩ := hf
  apply (stage14_algebraicPolynomialODE_iff_subfield _).mpr
  exact stage15_actualSubfieldODE_derivative (algebraicClosure ℚ ℂ).toSubfield
    (v5FactorialEntire f hd a hs)
    ((stage14_algebraicPolynomialODE_iff_subfield f).mp ho)

theorem v5_broad_actual_deriv {f : ℂ → ℂ} (hf : V5IsBroadEFunction f) :
    V5IsBroadEFunction (deriv f) := by
  have ho := v5_broad_actual_deriv_hasAlgebraicPolynomialODE hf
  obtain ⟨a, hd, hs, _, ha⟩ := hf
  exact ⟨(fun n => a (n+1)),
    differentiableOn_univ.mp (hd.differentiableOn.deriv isOpen_univ),
    strictE_egf_hasSum_derivative hd hs, ho,
    v5_broad_algebraicArithmetic_shift a ha 1⟩

theorem v5_broad_actual_iteratedDeriv (r : ℕ) {f : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) : V5IsBroadEFunction (iteratedDeriv r f) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact v5_broad_actual_deriv ih

/-- The literal factorial coefficients of the r-th actual derivative are shifted
by exactly r, not multiplied by any additional factorials. -/
theorem v5_broad_actual_iteratedDeriv_hasSum {f : ℂ → ℂ}
    (a : ℕ → AlgebraicComplex) (hd : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z))
    (r : ℕ) (z : ℂ) :
    HasSum (fun n => (a (n+r) : ℂ) * z^n / (n.factorial : ℂ))
      (iteratedDeriv r f z) := by
  induction r generalizing z with
  | zero => simpa only [Nat.add_zero, iteratedDeriv_zero] using hs z
  | succ r ih =>
    have hdr : Differentiable ℂ (iteratedDeriv r f) := by
      clear ih
      induction r with
      | zero => simpa only [iteratedDeriv_zero] using hd
      | succ j hj =>
        rw [iteratedDeriv_succ]
        exact differentiableOn_univ.mp (hj.differentiableOn.deriv isOpen_univ)
    have hsr : ∀ w, HasSum (fun n => (a (n+r) : ℂ) * w^n / (n.factorial : ℂ))
        (iteratedDeriv r f w) := by
      intro w
      exact ih w
    simpa only [iteratedDeriv_succ, Nat.add_right_comm, Nat.add_assoc] using
      strictE_egf_hasSum_derivative hdr hsr z

end StrictEUnit
#print axioms StrictEUnit.v5_broad_actual_deriv
#print axioms StrictEUnit.v5_broad_actual_iteratedDeriv
#print axioms StrictEUnit.v5_broad_actual_iteratedDeriv_hasSum
