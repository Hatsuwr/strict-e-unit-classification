import PolynomialDifferentialRightInverse
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div

/-!
# Polynomial constant-coefficient operators and exact resonance

The operator is the literal endomorphism evaluation P(D+c), not an abstract
surjectivity premise. A finite derivative recursion inverts the factor with
nonzero constant term; root multiplicity at c records the exact resonant factor.
No splitting or algebraic-closure assumption is used. These polynomial facts do
not construct a Frobenius basis or prove arithmetic growth or strict-E claims.
Source-only draft pending coordinated compiler verification.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Literal evaluation of the symbol at the formal derivative. -/
def polynomialDifferentialOperator (P : Polynomial K) : Module.End K (Polynomial K) :=
  Polynomial.aeval (Polynomial.derivative : Module.End K (Polynomial K)) P

/-- Its finite coefficient formula, retaining the original symbol. -/
theorem polynomialDifferentialOperator_apply (P f : Polynomial K) :
    polynomialDifferentialOperator P f =
      ∑ i ∈ P.support, P.coeff i •
        (Polynomial.derivative : Polynomial K → Polynomial K)^[i] f := by
  rw [polynomialDifferentialOperator, Polynomial.aeval_endomorphism, Polynomial.sum_def]
  simp only [Module.End.pow_apply]

theorem polynomialDifferentialOperator_mul (P Q f : Polynomial K) :
    polynomialDifferentialOperator (P * Q) f =
      polynomialDifferentialOperator P (polynomialDifferentialOperator Q f) := by
  simp only [polynomialDifferentialOperator, map_mul, Module.End.mul_apply]

theorem polynomialDifferentialOperator_commute (P Q f : Polynomial K) :
    polynomialDifferentialOperator P (polynomialDifferentialOperator Q f) =
      polynomialDifferentialOperator Q (polynomialDifferentialOperator P f) := by
  rw [← polynomialDifferentialOperator_mul, mul_comm, polynomialDifferentialOperator_mul]

/-- Separate the constant symbol coefficient from the derivative-divisible tail. -/
theorem polynomialDifferentialOperator_divX (P f : Polynomial K) :
    polynomialDifferentialOperator P f =
      polynomialDifferentialOperator P.divX f.derivative + P.coeff 0 • f := by
  have h := congrArg (fun Q : Polynomial K => polynomialDifferentialOperator Q f)
    P.divX_mul_X_add
  simpa only [polynomialDifferentialOperator, map_add, map_mul,
    Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply] using h.symm

/-- Every constant-coefficient polynomial operator is degree nonincreasing. -/
theorem polynomialDifferentialOperator_natDegree_le (P f : Polynomial K) :
    (polynomialDifferentialOperator P f).natDegree ≤ f.natDegree := by
  classical
  rw [polynomialDifferentialOperator_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_iterate_derivative f i).trans (Nat.sub_le _ _))

/-- All positive derivative terms vanish at the original top degree. -/
theorem polynomialDifferentialOperator_top_coeff (P f : Polynomial K) :
    (polynomialDifferentialOperator P f).coeff f.natDegree =
      P.coeff 0 * f.leadingCoeff := by
  classical
  have hder (i : ℕ) (hi : i ≠ 0) :
      ((Polynomial.derivative : Polynomial K → Polynomial K)^[i] f).coeff
        f.natDegree = 0 := by
    rw [Polynomial.coeff_iterate_derivative,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hi)), smul_zero]
  rw [polynomialDifferentialOperator_apply, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single 0]
  · simp only [Function.iterate_zero_apply, Polynomial.coeff_smul,
      Polynomial.coeff_natDegree, smul_eq_mul]
  · intro i _ hi
    simp only [Polynomial.coeff_smul, hder i hi, smul_zero]
  · intro h0
    simp only [Polynomial.not_mem_support_iff.mp h0, zero_smul, Polynomial.coeff_zero,
      zero_mul]

/-- Nonresonant operators preserve the degree of every polynomial. -/
theorem polynomialDifferentialOperator_natDegree (P f : Polynomial K)
    (hP : P.coeff 0 ≠ 0) :
    (polynomialDifferentialOperator P f).natDegree = f.natDegree := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero]
  · apply le_antisymm (polynomialDifferentialOperator_natDegree_le P f)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [polynomialDifferentialOperator_top_coeff]
    exact mul_ne_zero hP (Polynomial.leadingCoeff_ne_zero.mpr hf)

theorem polynomialDifferentialOperator_ne_zero (P f : Polynomial K)
    (hP : P.coeff 0 ≠ 0) (hf : f ≠ 0) : polynomialDifferentialOperator P f ≠ 0 := by
  intro h
  have hc := congrArg (fun Q : Polynomial K => Q.coeff f.natDegree) h
  dsimp only at hc
  rw [polynomialDifferentialOperator_top_coeff, Polynomial.coeff_zero] at hc
  exact (mul_ne_zero hP (Polynomial.leadingCoeff_ne_zero.mpr hf)) hc

theorem polynomialDifferentialOperator_injective (P : Polynomial K)
    (hP : P.coeff 0 ≠ 0) : Function.Injective (polynomialDifferentialOperator P) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  by_contra h
  exact polynomialDifferentialOperator_ne_zero P f hP h (LinearMap.mem_ker.mp hf)

/-- Finite geometric inversion of the derivative-divisible symbol tail. -/
def polynomialDifferentialOperatorInverseAux (P : Polynomial K) :
    ℕ → Polynomial K → Polynomial K
  | 0, _ => 0
  | n + 1, f => (P.coeff 0)⁻¹ • (f - polynomialDifferentialOperator P.divX
      (polynomialDifferentialOperatorInverseAux P n f.derivative))

theorem polynomialDifferentialOperatorInverseAux_rightInverse (P : Polynomial K)
    (hP : P.coeff 0 ≠ 0) (n : ℕ) (f : Polynomial K)
    (hf : (Polynomial.derivative : Polynomial K → Polynomial K)^[n] f = 0) :
    polynomialDifferentialOperator P (polynomialDifferentialOperatorInverseAux P n f) = f := by
  induction n generalizing f with
  | zero =>
    have hf0 : f = 0 := hf
    subst f
    simp only [polynomialDifferentialOperatorInverseAux, map_zero]
  | succ n ih =>
    have hfd : (Polynomial.derivative : Polynomial K → Polynomial K)^[n]
        f.derivative = 0 := by
      simpa only [Function.iterate_succ_apply] using hf
    have hq := ih f.derivative hfd
    rw [polynomialDifferentialOperatorInverseAux, map_smul, map_sub,
      polynomialDifferentialOperator_commute, hq,
      polynomialDifferentialOperator_divX, add_sub_cancel_left,
      smul_smul, inv_mul_cancel₀ hP, one_smul]

theorem polynomialDifferentialOperatorInverseAux_natDegree_le (P : Polynomial K)
    (n : ℕ) (f : Polynomial K) :
    (polynomialDifferentialOperatorInverseAux P n f).natDegree ≤ f.natDegree := by
  induction n generalizing f with
  | zero => simp [polynomialDifferentialOperatorInverseAux]
  | succ n ih =>
    exact (Polynomial.natDegree_smul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans
        (max_le le_rfl ((polynomialDifferentialOperator_natDegree_le _ _).trans
          ((ih f.derivative).trans
            ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _))))))

def polynomialDifferentialOperatorInverse (P f : Polynomial K) : Polynomial K :=
  polynomialDifferentialOperatorInverseAux P (f.natDegree + 1) f

@[simp] theorem polynomialDifferentialOperatorInverse_rightInverse (P f : Polynomial K)
    (hP : P.coeff 0 ≠ 0) :
    polynomialDifferentialOperator P (polynomialDifferentialOperatorInverse P f) = f :=
  polynomialDifferentialOperatorInverseAux_rightInverse P hP _ f
    (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _))

@[simp] theorem polynomialDifferentialOperatorInverse_leftInverse (P f : Polynomial K)
    (hP : P.coeff 0 ≠ 0) :
    polynomialDifferentialOperatorInverse P (polynomialDifferentialOperator P f) = f := by
  apply polynomialDifferentialOperator_injective P hP
  exact polynomialDifferentialOperatorInverse_rightInverse P _ hP

theorem polynomialDifferentialOperatorInverse_natDegree_le (P f : Polynomial K) :
    (polynomialDifferentialOperatorInverse P f).natDegree ≤ f.natDegree :=
  polynomialDifferentialOperatorInverseAux_natDegree_le P _ f

/-- The original shifted symbol evaluated at the actual endomorphism D+c. -/
def shiftedPolynomialDifferentialOperator (c : K) (P : Polynomial K) :
    Module.End K (Polynomial K) :=
  Polynomial.aeval (shiftedPolynomialDerivative c) P

/-- Shifting the symbol and shifting the derivative are exactly the same action. -/
theorem shiftedPolynomialDifferentialOperator_eq (c : K) (P : Polynomial K) :
    shiftedPolynomialDifferentialOperator c P =
      polynomialDifferentialOperator (P.comp (Polynomial.X + Polynomial.C c)) := by
  have ht : Polynomial.aeval (Polynomial.derivative : Module.End K (Polynomial K))
      (Polynomial.X + Polynomial.C c) = shiftedPolynomialDerivative c := by
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C,
      Module.algebraMap_end_eq_smul_id]
    rfl
  unfold shiftedPolynomialDifferentialOperator polynomialDifferentialOperator
  rw [Polynomial.aeval_comp, ht]

/-- The uniquely prescribed quotient after removing the full root multiplicity. -/
def polynomialDifferentialResidual (c : K) (P : Polynomial K) : Polynomial K :=
  P /ₘ (Polynomial.X - Polynomial.C c) ^ P.rootMultiplicity c

/-- The residual symbol is translated so its constant term is nonzero. -/
def polynomialDifferentialResidualShift (c : K) (P : Polynomial K) : Polynomial K :=
  (polynomialDifferentialResidual c P).comp (Polynomial.X + Polynomial.C c)

theorem polynomialDifferentialResidualShift_coeff_zero_ne (c : K)
    (P : Polynomial K) (hP : P ≠ 0) :
    (polynomialDifferentialResidualShift c P).coeff 0 ≠ 0 := by
  rw [polynomialDifferentialResidualShift, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    zero_add]
  exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hP

/-- Exact factorization of the original action, with resonance multiplicity q.
The residual acts after D^q; its order is justified by symbol multiplication. -/
theorem shiftedPolynomialDifferentialOperator_factor_apply (c : K)
    (P f : Polynomial K) :
    shiftedPolynomialDifferentialOperator c P f =
      polynomialDifferentialOperator (polynomialDifferentialResidualShift c P)
        ((Polynomial.derivative : Polynomial K → Polynomial K)^[P.rootMultiplicity c] f) := by
  have hfactor : P = polynomialDifferentialResidual c P *
      (Polynomial.X - Polynomial.C c) ^ P.rootMultiplicity c := by
    rw [polynomialDifferentialResidual, mul_comm,
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq]
  have hd : shiftedPolynomialDerivative c -
      algebraMap K (Module.End K (Polynomial K)) c = Polynomial.derivative := by
    rw [Module.algebraMap_end_eq_smul_id, shiftedPolynomialDerivative]
    exact add_sub_cancel_right _ _
  change Polynomial.aeval (shiftedPolynomialDerivative c) P f = _
  conv_lhs => rw [hfactor]
  rw [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hd,
    Module.End.mul_apply, Module.End.pow_apply]
  change shiftedPolynomialDifferentialOperator c (polynomialDifferentialResidual c P) _ = _
  rw [shiftedPolynomialDifferentialOperator_eq]
  rfl

/-- The P(c)≠0 branch is already invertible over an arbitrary field. -/
theorem shiftedPolynomialDifferentialOperator_nonresonant_rightInverse (c : K)
    (P f : Polynomial K) (hP : P.eval c ≠ 0) :
    shiftedPolynomialDifferentialOperator c P
      (polynomialDifferentialOperatorInverse (P.comp (Polynomial.X + Polynomial.C c)) f) = f := by
  rw [shiftedPolynomialDifferentialOperator_eq]
  apply polynomialDifferentialOperatorInverse_rightInverse
  simpa only [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add] using hP

section CharZero
variable [CharZero K]

/-- An explicit right inverse: invert the nonresonant factor, then integrate q times. -/
def shiftedPolynomialDifferentialRightInverse (c : K) (P f : Polynomial K) : Polynomial K :=
  polynomialIteratedPrimitive (P.rootMultiplicity c)
    (polynomialDifferentialOperatorInverse (polynomialDifferentialResidualShift c P) f)

@[simp] theorem shiftedPolynomialDifferentialRightInverse_apply (c : K)
    (P f : Polynomial K) (hP : P ≠ 0) :
    shiftedPolynomialDifferentialOperator c P (shiftedPolynomialDifferentialRightInverse c P f) =
      f := by
  rw [shiftedPolynomialDifferentialOperator_factor_apply,
    shiftedPolynomialDifferentialRightInverse, polynomialIteratedPrimitive_rightInverse]
  exact polynomialDifferentialOperatorInverse_rightInverse _ _
    (polynomialDifferentialResidualShift_coeff_zero_ne c P hP)

/-- The only logarithmic-degree cost is the exact resonance multiplicity. -/
theorem shiftedPolynomialDifferentialRightInverse_natDegree_le (c : K)
    (P f : Polynomial K) :
    (shiftedPolynomialDifferentialRightInverse c P f).natDegree ≤
      f.natDegree + P.rootMultiplicity c :=
  (polynomialIteratedPrimitive_natDegree_le _ _).trans
    (Nat.add_le_add_right (polynomialDifferentialOperatorInverse_natDegree_le _ _) _)

theorem shiftedPolynomialDifferentialOperator_surjective (c : K)
    (P : Polynomial K) (hP : P ≠ 0) :
    Function.Surjective (shiftedPolynomialDifferentialOperator c P) :=
  fun f => ⟨shiftedPolynomialDifferentialRightInverse c P f,
    shiftedPolynomialDifferentialRightInverse_apply c P f hP⟩

/-- Exact kernel, including the nonresonant q=0 and zero-polynomial boundaries. -/
theorem shiftedPolynomialDifferentialOperator_kernel_iff (c : K)
    (P f : Polynomial K) (hP : P ≠ 0) :
    shiftedPolynomialDifferentialOperator c P f = 0 ↔
      f.degree < (P.rootMultiplicity c : WithBot ℕ) := by
  rw [shiftedPolynomialDifferentialOperator_factor_apply]
  have hzero : polynomialDifferentialOperator (polynomialDifferentialResidualShift c P)
      ((Polynomial.derivative : Polynomial K → Polynomial K)^[P.rootMultiplicity c] f) = 0 ↔
      (Polynomial.derivative : Polynomial K → Polynomial K)^[P.rootMultiplicity c] f = 0 := by
    constructor
    · intro h
      apply polynomialDifferentialOperator_injective _
        (polynomialDifferentialResidualShift_coeff_zero_ne c P hP)
      simpa only [map_zero] using h
    · rintro h
      rw [h, map_zero]
  exact hzero.trans (polynomial_iterate_derivative_eq_zero_iff_degree _ f)

/-- Every polynomial solution is the explicit particular solution plus exactly
the degree<q resonant freedom, with no missing or spurious solutions. -/
theorem shiftedPolynomialDifferentialOperator_solution_iff (c : K)
    (P g f : Polynomial K) (hP : P ≠ 0) :
    shiftedPolynomialDifferentialOperator c P f = g ↔
      ∃ r : Polynomial K, r.degree < (P.rootMultiplicity c : WithBot ℕ) ∧
        f = shiftedPolynomialDifferentialRightInverse c P g + r := by
  constructor
  · intro hf
    refine ⟨f - shiftedPolynomialDifferentialRightInverse c P g, ?_, ?_⟩
    · apply (shiftedPolynomialDifferentialOperator_kernel_iff c P _ hP).mp
      rw [map_sub, hf, shiftedPolynomialDifferentialRightInverse_apply c P g hP, sub_self]
    · abel
  · rintro ⟨r, hr, rfl⟩
    rw [map_add, shiftedPolynomialDifferentialRightInverse_apply c P g hP,
      (shiftedPolynomialDifferentialOperator_kernel_iff c P r hP).mpr hr, add_zero]

end CharZero
end StrictEUnit
