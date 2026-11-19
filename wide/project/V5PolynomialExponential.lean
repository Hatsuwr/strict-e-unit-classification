import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace StrictEUnit

/-- Polynomial antiderivatives exist over the actual characteristic-zero
coefficient field, normalized to vanish at zero. -/
theorem v5_polynomial_primitive {k : Type*} [Field k] [CharZero k] (p : Polynomial k) :
    ∃ P : Polynomial k, P.derivative = p ∧ P.eval 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨A,hA,hA0⟩ := ha
    obtain ⟨B,hB,hB0⟩ := hb
    refine ⟨A+B, ?_, ?_⟩
    · rw [Polynomial.derivative_add,hA,hB]
    · rw [Polynomial.eval_add,hA0,hB0,zero_add]
  | monomial n c =>
    let d : k := (n+1 : ℕ)
    have hd : d ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
    refine ⟨Polynomial.monomial (n+1) (c/d), ?_, ?_⟩
    · rw [Polynomial.derivative_monomial, Nat.add_sub_cancel]
      congr 1
      change c/d*d = c
      exact div_mul_cancel₀ c hd
    · simp [Polynomial.eval_monomial]

/-- An entire solution of the polynomial scalar equation on the punctured
plane is its origin value times an exponential of an algebraic primitive. -/
theorem v5_entire_polynomial_ode_exponential {k : Type*} [Field k] [CharZero k]
    (f : k →+* ℂ) (p : Polynomial k) (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    (hODE : ∀ z ≠ 0, deriv W z = p.eval₂ f z * W z) :
    ∃ P : Polynomial k, P.derivative = p ∧ P.eval 0 = 0 ∧
      ∀ z, W z = W 0 * Complex.exp (P.eval₂ f z) := by
  obtain ⟨P,hP,hP0⟩ := v5_polynomial_primitive p
  let Q := P.map f
  have hQ0 : Q.eval 0 = 0 := by
    change (P.map f).eval 0 = 0
    rw [Polynomial.eval_zero_map,hP0,map_zero]
  have hder (z : ℂ) :
      HasDerivAt (fun z => Q.eval z) (p.eval₂ f z) z := by
    simpa only [Q, Polynomial.derivative_map, hP, Polynomial.eval_map] using Q.hasDerivAt z
  have hODE' : ∀ z, deriv W z = p.eval₂ f z * W z := by
    have hcont : Continuous (deriv W) :=
      (differentiableOn_univ.mp (hW.differentiableOn.deriv isOpen_univ)).continuous
    have hc2 : Continuous (fun z => p.eval₂ f z * W z) := by
      apply Continuous.mul _ hW.continuous
      have hp : Differentiable ℂ (fun z => (p.map f).eval z) :=
        fun z => ((p.map f).hasDerivAt z).differentiableAt
      simpa only [Polynomial.eval_map] using hp.continuous
    have hc := isClosed_eq hcont hc2
    have hs : ({0}ᶜ : Set ℂ) ⊆ {z | deriv W z = p.eval₂ f z * W z} := by
      intro z hz
      exact hODE z (by simpa using hz)
    have he := closure_minimal hs hc
    rw [(dense_compl_singleton (0:ℂ)).closure_eq] at he
    exact fun z => he (Set.mem_univ z)
  let G : ℂ → ℂ := fun z => W z * Complex.exp (-(Q.eval z))
  have hG (z : ℂ) : HasDerivAt G 0 z := by
    have h := ((hW z).hasDerivAt).mul
      ((Complex.hasDerivAt_exp (-(Q.eval z))).comp z (hder z).neg)
    rw [hODE' z] at h
    simp only [Function.comp_apply] at h
    convert h using 1
    ring
  refine ⟨P,hP,hP0,fun z => ?_⟩
  have hc := is_const_of_deriv_eq_zero (fun z => (hG z).differentiableAt)
    (fun z => (hG z).deriv) z 0
  dsimp [G] at hc
  rw [hQ0, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← Polynomial.eval_map]
  calc
    W z = (W z * Complex.exp (-(Q.eval z))) * Complex.exp (Q.eval z) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [hc]

end StrictEUnit
#print axioms StrictEUnit.v5_polynomial_primitive
#print axioms StrictEUnit.v5_entire_polynomial_ode_exponential
