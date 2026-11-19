import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
namespace StrictEUnit

/-- Actual entire complex functions with scalars restricted to k. -/
def v5EntireSubalgebra (k : Type*) [CommRing k] [Algebra k ℂ] :
    Subalgebra k (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f}
  zero_mem' := differentiable_const 0
  one_mem' := differentiable_const 1
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  algebraMap_mem' := fun a => differentiable_const (algebraMap k ℂ a)

variable (k : Type*) [CommRing k] [Algebra k ℂ]

@[simp] theorem mem_v5EntireSubalgebra (f : ℂ → ℂ) :
    f ∈ v5EntireSubalgebra k ↔ Differentiable ℂ f := Iff.rfl

/-- The complex identity theorem on the connected plane proves no zero
divisors; the carrier is not a ring of formal series or germs. -/
instance v5EntireSubalgebra_noZeroDivisors : NoZeroDivisors (v5EntireSubalgebra k) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro f g hfg
    have hpoint : ∀ z ∈ (Set.univ : Set ℂ), f.val z * g.val z = 0 := by
      intro z _
      exact congrArg (fun h : v5EntireSubalgebra k => h.val z) hfg
    have hf : AnalyticOnNhd ℂ f.val Set.univ := fun z _ => f.property.analyticAt z
    have hg : AnalyticOnNhd ℂ g.val Set.univ := fun z _ => g.property.analyticAt z
    rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hf hg hpoint
      isPreconnected_univ with h | h
    · exact Or.inl (Subtype.ext (funext fun z => h z (Set.mem_univ z)))
    · exact Or.inr (Subtype.ext (funext fun z => h z (Set.mem_univ z)))

instance v5EntireSubalgebra_isDomain : IsDomain (v5EntireSubalgebra k) :=
  NoZeroDivisors.to_isDomain _

/-- Translation f(z) ↦ f(z+c), as an automorphism fixing all k scalars. -/
def v5EntireTranslation (c : ℂ) :
    v5EntireSubalgebra k ≃ₐ[k] v5EntireSubalgebra k where
  toFun f := ⟨fun z => f.val (z + c), f.property.comp (differentiable_id.add_const c)⟩
  invFun f := ⟨fun z => f.val (z - c), f.property.comp (differentiable_id.sub_const c)⟩
  left_inv f := by apply Subtype.ext; funext z; simp
  right_inv f := by apply Subtype.ext; funext z; simp
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' a := rfl

@[simp] theorem v5EntireTranslation_apply (c : ℂ) (f : v5EntireSubalgebra k) (z : ℂ) :
    (v5EntireTranslation k c f).val z = f.val (z + c) := rfl

@[simp] theorem v5EntireTranslation_pow_apply (c : ℂ) (n : ℕ)
    (f : v5EntireSubalgebra k) (z : ℂ) :
    ((v5EntireTranslation k c ^ n) f).val z = f.val (z + (n : ℂ) * c) := by
  induction n generalizing f z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change ((v5EntireTranslation k c ^ n) (v5EntireTranslation k c f)).val z = _
    rw [ih, v5EntireTranslation_apply]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc]

/-- A k-valued input scalar is evaluated through the specified embedding. -/
def v5EntireEvaluation (z : ℂ) : v5EntireSubalgebra k →ₐ[k] ℂ where
  toFun f := f.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem v5EntireEvaluation_apply (z : ℂ) (f : v5EntireSubalgebra k) :
    v5EntireEvaluation k z f = f.val z := rfl

end StrictEUnit
#print axioms StrictEUnit.v5EntireSubalgebra_noZeroDivisors
#print axioms StrictEUnit.v5EntireSubalgebra_isDomain
#print axioms StrictEUnit.v5EntireTranslation
#print axioms StrictEUnit.v5EntireTranslation_pow_apply
#print axioms StrictEUnit.v5EntireEvaluation
