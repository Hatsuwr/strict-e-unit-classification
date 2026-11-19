import V5PolynomialExponential
import V5NormalizedLaurentTailOver
import V5PuncturedKummerDerivative
import V5ArithmeticTensorPostLift

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
open scoped TensorProduct
namespace StrictEUnit

/-- Algebraic prefactor plus polynomial logarithmic derivative gives the
required algebraic exponential value. -/
theorem v5_algebraic_exponential_mark (W : entireFunctionAlgebra)
    (hw : W.val 0 ≠ 0) (ha : W.val 0 ∈ (algebraicClosure ℚ ℂ).toSubfield)
    (p : Polynomial AlgebraicComplex)
    (heq : ∀ z ≠ 0, deriv W.val z = p.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * W.val z) :
    ∃ (α β : AlgebraicComplex), α ≠ 0 ∧ W.val 1 = (α : ℂ) * Complex.exp (β : ℂ) := by
  let f := (algebraicClosure ℚ ℂ).val.toRingHom
  obtain ⟨P, _, _, hP⟩ := v5_entire_polynomial_ode_exponential f p W.val W.property heq
  let α : AlgebraicComplex := ⟨W.val 0, ha⟩
  refine ⟨α,P.eval 1,fun hn => hw (congrArg Subtype.val hn),?_⟩
  have hmark : P.eval₂ f 1 = f (P.eval 1) := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval_one_map]
  calc
    W.val 1 = W.val 0 * Complex.exp (P.eval₂ f 1) := hP 1
    _ = _ := by rw [hmark]; rfl


/-- An already lifted arithmetic unit with an actual Laurent Euler equation
has the required algebraic exponential mark. -/
theorem v5_punctured_arithmetic_laurent_ode_mark
    (U dU : V5PuncturedFunctions) (hd : V5HasPuncturedDeriv U dU)
    (W : entireFunctionAlgebra) (m : ℤ)
    (hW0 : W.val 0 ≠ 0) (ha : W.val 0 ∈ (algebraicClosure ℚ ℂ).toSubfield)
    (hrep : ∀ z : ℂˣ, U z = (z : ℂ)^m * W.val z)
    (L : LaurentPolynomial AlgebraicComplex)
    (hEuler : ∀ z : ℂˣ, (z : ℂ) * dU z = arithmeticLaurentEvaluation z L * U z) :
    ∃ (α β : AlgebraicComplex), α ≠ 0 ∧ U 1 = (α : ℂ) * Complex.exp (β : ℂ) := by
  let f := (algebraicClosure ℚ ℂ).val.toRingHom
  obtain ⟨u, hu, hud⟩ := hd
  let b (z : ℂ) : ℂ := if hz : z = 0 then 0 else arithmeticLaurentEvaluation (Units.mk0 z hz) L
  have hb (z : ℂ) (hz : z ≠ 0) :
      b z = LaurentPolynomial.eval₂ f (Units.mk0 z hz) L := by
    rw [show b z = arithmeticLaurentEvaluation (Units.mk0 z hz) L by simp [b,hz]]
    rfl
  have he (z : ℂ) (hz : z ≠ 0) : u z = z^m * W.val z :=
    (hu (Units.mk0 z hz)).trans (hrep (Units.mk0 z hz))
  have hd' (z : ℂ) (hz : z ≠ 0) : HasDerivAt u (b z*u z/z) z := by
    let e := Units.mk0 z hz
    have h := hEuler e
    change z * dU e = _ at h
    rw [← hu e] at h
    have hh : dU e = b z * u z / z := by
      apply (eq_div_iff hz).mpr
      rw [mul_comm, h, hb z hz]
      rfl
    rw [← hh]
    exact hud e
  obtain ⟨Q,hQ⟩ := v5_normalized_laurent_euler_tail_over f u W.val b m W.property hW0 hd' he L hb
  have hODE (z : ℂ) (hz : z ≠ 0) :
      deriv W.val z = Q.eval₂ f z * W.val z := by
    have hn := v5_normalized_euler_equation u W.val b m W.property hd' he z hz
    have hval : b z = (m : ℂ) + z * Q.eval₂ f z := by
      rw [hb z hz, hQ, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_add,
        Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, map_intCast]
      rfl
    rw [hval] at hn
    apply mul_left_cancel₀ hz
    calc
      z * deriv W.val z = ((m : ℂ) + z * Q.eval₂ f z - (m : ℂ)) * W.val z := hn
      _ = z * (Q.eval₂ f z * W.val z) := by ring
  obtain ⟨α,β,hα,hvalue⟩ := v5_algebraic_exponential_mark W hW0 ha Q hODE
  have hm : U 1 = W.val 1 := by
    simpa only [Units.val_one, one_zpow, one_mul] using hrep 1
  exact ⟨α,β,hα,hm.trans hvalue⟩


/-- Conditional end of v5 on the actual wide solution algebra. Any lifted
unit whose image satisfies the checked form of the Euler equation has the
required marked value. This constructs neither the lift nor its ODE. -/
theorem v5_actual_wide_kummer_laurent_ode_mark {ι : Type} (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    {D : Type*} [CommRing D] [Algebra V5LaurentBase D]
    (q : ℕ) (hq : 0 < q) (ω : D →+* V5LaurentBase)
    (hω : ∀ p, ω (algebraMap V5LaurentBase D p) = v5LaurentPower q p) :
    ∃ η : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D →+*
        v5MeromorphicZeroAlgebra AlgebraicComplex,
      (∀ s d z, (η (s ⊗ₜ[V5LaurentBase] d)).val z = s.val (z^q) *
        arithmeticLaurentEvaluation z (ω d)) ∧
      (∀ u : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D, IsUnit u →
        ∀ (du : V5PuncturedFunctions) (L : V5LaurentBase),
          V5HasPuncturedDeriv (η u).val du →
          (∀ z : ℂˣ, (z : ℂ) * du z = arithmeticLaurentEvaluation z L * (η u).val z) →
          ∃ (α β : AlgebraicComplex), α ≠ 0 ∧ (η u).val 1 = (α : ℂ) * Complex.exp (β : ℂ)) := by
  obtain ⟨η,hη,hunit⟩ := v5_actual_wide_kummer_tensor_unit f hf q hq ω hω
  refine ⟨η,hη,?_⟩
  intro u hu du L hd he
  obtain ⟨m,W,hW,hrep,_,ha⟩ := hunit u hu
  exact v5_punctured_arithmetic_laurent_ode_mark (η u).val du hd W m (hW 0) ha hrep L he

end StrictEUnit
#print axioms StrictEUnit.v5_algebraic_exponential_mark
#print axioms StrictEUnit.v5_punctured_arithmetic_laurent_ode_mark
#print axioms StrictEUnit.v5_actual_wide_kummer_laurent_ode_mark
