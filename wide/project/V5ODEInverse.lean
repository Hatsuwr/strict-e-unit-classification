import V5ODEDifferential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

noncomputable section
namespace StrictEUnit

/-- The opposite-algebra construction solves the right inverse-side ODE. -/
theorem v5_finite_exponential_right_ode_exists
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) (V0 : A) :
    ∃ V : ℂ → A, V 0 = V0 ∧ ∀ z : ℂ,
      HasDerivAt V (-(V z * (∑ j ∈ J, Complex.exp (c j*z) • B j))) z := by
  obtain ⟨W, hW0, hW⟩ := v5_finite_exponential_ode_exists
    J (fun j => MulOpposite.op (-B j)) c (MulOpposite.op V0)
  refine ⟨fun z => MulOpposite.unop (W z), ?_, ?_⟩
  · simp only [hW0, MulOpposite.unop_op]
  · intro z
    have h := ((MulOpposite.opContinuousLinearEquiv ℂ (M := A)).symm.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt z (hW z)
    convert h using 1
    ·
      simp [Finset.sum_neg_distrib, ← Finset.smul_sum]

/-- Left and right ODE solutions have constant reverse product. -/
theorem v5_ode_reverse_product_constant
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D U V : ℂ → A)
    (hU : ∀ z, HasDerivAt U (D z * U z) z)
    (hV : ∀ z, HasDerivAt V (-(V z * D z)) z) (z : ℂ) :
    V z * U z = V 0 * U 0 := by
  have hzero : ∀ z, HasDerivAt (fun w => V w * U w) 0 z := by
    intro z
    convert (hV z).mul (hU z) using 1
    simp only [neg_mul, mul_assoc, neg_add_cancel]
  exact is_const_of_deriv_eq_zero (fun z => (hzero z).differentiableAt)
    (fun z => (hzero z).deriv) z 0

/-- Both ODE solutions exist, with reverse product equal to one, in every
complete normed complex algebra. No direct-finiteness is claimed here. -/
theorem v5_finite_exponential_ode_left_inverse_exists
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) :
    ∃ U V : ℂ → A, U 0 = 1 ∧ V 0 = 1 ∧
      (∀ z, HasDerivAt U ((∑ j ∈ J, Complex.exp (c j*z) • B j) * U z) z) ∧
      (∀ z, HasDerivAt V (-(V z * (∑ j ∈ J, Complex.exp (c j*z) • B j))) z) ∧
      ∀ z, V z * U z = 1 := by
  obtain ⟨U, hU0, hU⟩ := v5_finite_exponential_ode_exists J B c (1 : A)
  obtain ⟨V, hV0, hV⟩ := v5_finite_exponential_right_ode_exists J B c (1 : A)
  refine ⟨U, V, hU0, hV0, hU, hV, ?_⟩
  intro z
  rw [v5_ode_reverse_product_constant _ U V hU hV z, hU0, hV0, mul_one]

/-- Direct-finite algebras upgrade the constructed left inverse to a
pointwise two-sided inverse. -/
theorem v5_finite_exponential_ode_inverse_exists
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (hfinite : ∀ a b : A, a * b = 1 → b * a = 1)
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) :
    ∃ U V : ℂ → A, U 0 = 1 ∧ V 0 = 1 ∧
      (∀ z, HasDerivAt U ((∑ j ∈ J, Complex.exp (c j*z) • B j) * U z) z) ∧
      (∀ z, HasDerivAt V (-(V z * (∑ j ∈ J, Complex.exp (c j*z) • B j))) z) ∧
      ∀ z, V z * U z = 1 ∧ U z * V z = 1 := by
  obtain ⟨U, V, hU0, hV0, hU, hV, hVU⟩ := v5_finite_exponential_ode_left_inverse_exists J B c
  exact ⟨U, V, hU0, hV0, hU, hV, fun z => ⟨hVU z, hfinite _ _ (hVU z)⟩⟩

/-- A genuine algebra identification with finite square matrices supplies
the direct-finiteness premise, independently of the chosen valid norm. -/
theorem v5_matrix_algebra_direct_finite
    {A n : Type*} [Ring A] [Algebra ℂ A] [Fintype n] [DecidableEq n]
    (e : A ≃ₐ[ℂ] Matrix n n ℂ) (a b : A) (h : a * b = 1) : b * a = 1 := by
  apply e.injective
  have hm : e a * e b = 1 := by simpa only [map_mul, map_one] using congrArg e h
  simpa only [map_mul, map_one] using Matrix.mul_eq_one_comm.mp hm

/-- Complete normed matrix algebras have actual globally differentiable
fundamental solutions and their two-sided inverse solutions. -/
theorem v5_finite_exponential_matrix_ode_inverse_exists
    {A ι n : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Fintype n] [DecidableEq n] (e : A ≃ₐ[ℂ] Matrix n n ℂ)
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) :
    ∃ U V : ℂ → A, U 0 = 1 ∧ V 0 = 1 ∧
      (∀ z, HasDerivAt U ((∑ j ∈ J, Complex.exp (c j*z) • B j) * U z) z) ∧
      (∀ z, HasDerivAt V (-(V z * (∑ j ∈ J, Complex.exp (c j*z) • B j))) z) ∧
      ∀ z, V z * U z = 1 ∧ U z * V z = 1 :=
  v5_finite_exponential_ode_inverse_exists (v5_matrix_algebra_direct_finite e) J B c

end StrictEUnit
#print axioms StrictEUnit.v5_finite_exponential_right_ode_exists
#print axioms StrictEUnit.v5_ode_reverse_product_constant
#print axioms StrictEUnit.v5_finite_exponential_ode_left_inverse_exists
#print axioms StrictEUnit.v5_finite_exponential_ode_inverse_exists
#print axioms StrictEUnit.v5_matrix_algebra_direct_finite
#print axioms StrictEUnit.v5_finite_exponential_matrix_ode_inverse_exists
