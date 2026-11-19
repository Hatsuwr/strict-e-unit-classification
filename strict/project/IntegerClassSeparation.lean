import IntegerClassSharedNormalization

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def IntegerExponentRelated (rho sigma : K) : Prop :=
  ∃ z : ℤ,rho-sigma=(z : K)

theorem integerExponentRelated_equivalence :
    Equivalence (IntegerExponentRelated (K:=K)) := by
  refine ⟨?_,?_,?_⟩
  · intro rho
    exact ⟨0,by simp⟩
  · rintro rho sigma ⟨z,hz⟩
    refine ⟨-z,?_⟩
    rw [Int.cast_neg,← hz]
    ring
  · rintro rho sigma tau ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨a+b,?_⟩
    rw [Int.cast_add,← ha,← hb]
    ring

/-- Distinct classes stay distinct after every integer Laurent shift. -/
theorem integerExponent_distinct_translates (rho sigma : K)
    (h : ¬IntegerExponentRelated rho sigma) (a b : ℤ) :
    rho+(a : K)≠sigma+(b : K) := by
  intro he
  apply h
  refine ⟨b-a,?_⟩
  rw [Int.cast_sub]
  linear_combination he

/-- A falling filter belonging to one class has NO pivot zeros on another
class, at any integer shift. Thus within-class filters cannot by themselves
be treated as projections that remove the other classes. -/
theorem integerClassFallingComposite_otherClass_pivot (rho sigma : K)
    (h : ¬IntegerExponentRelated rho sigma) {q : ℕ} (s : Fin q → ℤ)
    (ms : Fin q → ℕ) (a : ℤ) :
    (integerClassFallingComposite rho s ms).eval (sigma+(a : K))≠0 := by
  simp only [integerClassFallingComposite,fallingCompositeSymbol,Polynomial.eval_prod,
    Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,id_eq,
    normalizedFallingSymbol,Polynomial.eval_mul,Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk he
  apply h
  refine ⟨a-s i-(k : ℤ),?_⟩
  push_cast
  linear_combination -he

/-- The action on every other class is actually bijective, not annihilating.
This is an exact obstruction to an unjustified class-projection shortcut. -/
theorem integerClassFallingComposite_otherClass_bijective (rho sigma : K)
    (h : ¬IntegerExponentRelated rho sigma) {q : ℕ} (s : Fin q → ℤ)
    (ms : Fin q → ℕ) (a : ℤ) :
    Function.Bijective (shiftedPolynomialDifferentialOperator (sigma+(a : K))
      (integerClassFallingComposite rho s ms)) := by
  have hp := integerClassFallingComposite_otherClass_pivot rho sigma h s ms a
  have hc : ((integerClassFallingComposite rho s ms).comp
      (Polynomial.X+Polynomial.C (sigma+(a : K)))).coeff 0≠0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,zero_add] using hp
  rw [shiftedPolynomialDifferentialOperator_eq]
  refine ⟨polynomialDifferentialOperator_injective _ hc,?_⟩
  intro f
  exact ⟨polynomialDifferentialOperatorInverse _ f,
    polynomialDifferentialOperatorInverse_rightInverse _ f hc⟩

end StrictEUnit
end
