import Stage14ActualAnalyticODETransfer
import StrictEScalarFunctionClosure
import StrictEAlgebraicRescaling

/-!
# Actual strict E-function and strict E-value ring closure

The differential equations, factorial series, entire differentiability,
conjugate bounds, and common-denominator conditions are all proved for sums
and products. The genuine numerical class therefore forms a subring, and the
original numerical unit predicate is connected to its actual units.
-/
noncomputable section
namespace StrictEUnit

/-- Full closure under addition, using the actual analytic ODE theorem. -/
theorem strictEFunction_add {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g) :
    IsStrictEFunction (fun z => f z + g z) := by
  obtain ⟨a, hd, hs, ha⟩ := strictEFunction_add_analytic_arithmetic hf hg
  exact ⟨a, hd, hs, strictEFunction_add_hasAlgebraicPolynomialODE hf hg, ha⟩

/-- Full closure under multiplication, including the nonzero polynomial ODE. -/
theorem strictEFunction_mul {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g) :
    IsStrictEFunction (fun z => f z * g z) := by
  obtain ⟨a, hd, hs, ha⟩ := strictEFunction_mul_analytic_arithmetic hf hg
  exact ⟨a, hd, hs, strictEFunction_mul_hasAlgebraicPolynomialODE hf hg, ha⟩

/-- Actual strict E-values are closed under addition after the proved
normalization of both algebraic arguments to one. -/
theorem strictEValue_add {u v : ℂ} (hu : IsStrictEValue u) (hv : IsStrictEValue v) :
    IsStrictEValue (u + v) := by
  obtain ⟨f, hf, hfu⟩ := (strictEValue_iff_at_one u).mp hu
  obtain ⟨g, hg, hgv⟩ := (strictEValue_iff_at_one v).mp hv
  exact (strictEValue_iff_at_one (u + v)).mpr
    ⟨fun z => f z + g z, strictEFunction_add hf hg, by simp only [hfu, hgv]⟩

/-- Actual strict E-values are closed under multiplication. -/
theorem strictEValue_mul {u v : ℂ} (hu : IsStrictEValue u) (hv : IsStrictEValue v) :
    IsStrictEValue (u * v) := by
  obtain ⟨f, hf, hfu⟩ := (strictEValue_iff_at_one u).mp hu
  obtain ⟨g, hg, hgv⟩ := (strictEValue_iff_at_one v).mp hv
  exact (strictEValue_iff_at_one (u * v)).mpr
    ⟨fun z => f z * g z, strictEFunction_mul hf hg, by simp only [hfu, hgv]⟩

/-- Actual strict E-values are closed under negation. -/
theorem strictEValue_neg {u : ℂ} (hu : IsStrictEValue u) : IsStrictEValue (-u) := by
  obtain ⟨f, hf, hfu⟩ := (strictEValue_iff_at_one u).mp hu
  exact (strictEValue_iff_at_one (-u)).mpr
    ⟨fun z => -f z, strictEFunction_neg hf, by simp only [hfu]⟩

/-- The numerical strict E-value class itself, not an artificially generated
larger ring, is now a genuine subring of the complex numbers. -/
def strictEValueSubring : Subring ℂ where
  carrier := {u | IsStrictEValue u}
  zero_mem' := by simpa using algebraic_isStrictEValue (0 : AlgebraicComplex)
  one_mem' := by simpa using algebraic_isStrictEValue (1 : AlgebraicComplex)
  add_mem' := strictEValue_add
  mul_mem' := strictEValue_mul
  neg_mem' := strictEValue_neg

/-- Membership agrees exactly with the original strict E-value predicate. -/
@[simp] theorem mem_strictEValueSubring (u : ℂ) :
    u ∈ strictEValueSubring ↔ IsStrictEValue u := Iff.rfl

/-- The actual algebraic constants belong to the actual strict E-value ring. -/
theorem algebraic_mem_strictEValueSubring (α : AlgebraicComplex) :
    (α : ℂ) ∈ strictEValueSubring := algebraic_isStrictEValue α

/-- The original numerical unit predicate is exactly the image of actual units
of the newly proved strict E-value subring. The original definition is unchanged. -/
theorem strictEValueUnit_iff_exists_unit (u : ℂ) :
    IsStrictEValueUnit u ↔
      ∃ v : strictEValueSubringˣ, ((v : strictEValueSubring) : ℂ) = u := by
  constructor
  · rintro ⟨hne, hu, hi⟩
    let v : strictEValueSubringˣ :=
      { val := ⟨u, hu⟩
        inv := ⟨u⁻¹, hi⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hne)
        inv_val := Subtype.ext (inv_mul_cancel₀ hne) }
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    have hne : ((v : strictEValueSubring) : ℂ) ≠ 0 :=
      (Units.map strictEValueSubring.subtype.toMonoidHom v).ne_zero
    have hinv : (((v⁻¹ : strictEValueSubringˣ) : strictEValueSubring) : ℂ) =
        (((v : strictEValueSubring) : ℂ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun x : strictEValueSubring => (x : ℂ)) v.inv_val
    refine ⟨hne, (v : strictEValueSubring).property, ?_⟩
    rw [← hinv]
    exact ((v⁻¹ : strictEValueSubringˣ) : strictEValueSubring).property

/-- For a member of the actual ring, the original numerical unit predicate
is precisely the ordinary ring-theoretic `IsUnit` proposition. -/
theorem strictEValueUnit_iff_isUnit (u : strictEValueSubring) :
    IsStrictEValueUnit (u : ℂ) ↔ IsUnit u := by
  rw [strictEValueUnit_iff_exists_unit]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, congrArg (fun x : strictEValueSubring => (x : ℂ)) hv⟩

end StrictEUnit
