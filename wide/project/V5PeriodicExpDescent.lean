import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open scoped Topology
namespace StrictEUnit

/-- A principal-log representative; periodicity removes its branch jump. -/
def v5PeriodicExpDescent (f : ℂ → ℂ) (q : ℂ) (t : ℂ) : ℂ :=
  f (q * Complex.log t)

theorem v5_periodic_eq_of_exp_eq (f : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hper : Function.Periodic f (q * (2 * Real.pi * Complex.I)))
    {u v : ℂ} (h : Complex.exp (u / q) = Complex.exp (v / q)) : f u = f v := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have huv : u = v + (n : ℂ) * (q * (2 * Real.pi * Complex.I)) := by
    have he := congrArg (fun z : ℂ => q * z) hn
    field_simp at he
    linear_combination he
  rw [huv]
  exact hper.int_mul n v

theorem v5PeriodicExpDescent_exp (f : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hper : Function.Periodic f (q * (2 * Real.pi * Complex.I))) (w : ℂ) :
    v5PeriodicExpDescent f q (Complex.exp (w / q)) = f w := by
  apply v5_periodic_eq_of_exp_eq f q hq hper
  rw [mul_div_cancel_left₀ _ hq, Complex.exp_log (Complex.exp_ne_zero _)]

@[simp] theorem v5PeriodicExpDescent_one (f : ℂ → ℂ) (q : ℂ) :
    v5PeriodicExpDescent f q 1 = f 0 := by
  simp [v5PeriodicExpDescent]

/-- A logarithm centered at any nonzero t₀ gives a valid local representative. -/
theorem v5PeriodicExpDescent_local (f : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hper : Function.Periodic f (q * (2 * Real.pi * Complex.I)))
    (t₀ t : ℂ) (h₀ : t₀ ≠ 0) (ht : t ≠ 0) :
    v5PeriodicExpDescent f q t =
      f (q * (Complex.log t₀ + Complex.log (t / t₀))) := by
  apply v5_periodic_eq_of_exp_eq f q hq hper
  rw [mul_div_cancel_left₀ _ hq, mul_div_cancel_left₀ _ hq,
    Complex.exp_log ht, Complex.exp_add, Complex.exp_log h₀,
    Complex.exp_log (div_ne_zero ht h₀)]
  field_simp

/-- The descended function is complex differentiable everywhere on C*,
including points on the principal logarithm's branch cut. -/
theorem v5PeriodicExpDescent_differentiableAt (f : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hf : Differentiable ℂ f)
    (hper : Function.Periodic f (q * (2 * Real.pi * Complex.I)))
    (t₀ : ℂ) (h₀ : t₀ ≠ 0) :
    DifferentiableAt ℂ (v5PeriodicExpDescent f q) t₀ := by
  have hlog : DifferentiableAt ℂ (fun t : ℂ => Complex.log (t / t₀)) t₀ := by
    have hb : DifferentiableAt ℂ Complex.log (t₀ / t₀) :=
      Complex.differentiableAt_log (by simpa only [div_self h₀] using Complex.one_mem_slitPlane)
    exact hb.comp (f := fun t : ℂ => t / t₀) t₀ (differentiableAt_id.div_const t₀)
  have hd : DifferentiableAt ℂ
      (fun t : ℂ => f (q * (Complex.log t₀ + Complex.log (t / t₀)))) t₀ :=
    (hf _).comp t₀ ((hlog.const_add _).const_mul q)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds h₀] with t ht
  exact v5PeriodicExpDescent_local f q hq hper t₀ t h₀ ht

/-- Positive-integer Kummer-cover interface with the evaluation and mark
identities bundled with holomorphy on the punctured complex plane. -/
theorem v5_periodic_entire_descends (f : ℂ → ℂ) (q : ℕ) (hq : 0 < q)
    (hf : Differentiable ℂ f)
    (hper : Function.Periodic f ((q : ℂ) * (2 * Real.pi * Complex.I))) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {t | t ≠ 0} ∧
      (∀ w : ℂ, F (Complex.exp (w / (q : ℂ))) = f w) ∧ F 1 = f 0 := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  refine ⟨v5PeriodicExpDescent f q, ?_, ?_, v5PeriodicExpDescent_one f q⟩
  · intro t ht
    exact (v5PeriodicExpDescent_differentiableAt f q hqC hf hper t ht).differentiableWithinAt
  · exact v5PeriodicExpDescent_exp f q hqC hper

end StrictEUnit
#print axioms StrictEUnit.v5_periodic_eq_of_exp_eq
#print axioms StrictEUnit.v5PeriodicExpDescent_exp
#print axioms StrictEUnit.v5PeriodicExpDescent_one
#print axioms StrictEUnit.v5PeriodicExpDescent_local
#print axioms StrictEUnit.v5PeriodicExpDescent_differentiableAt

#print axioms StrictEUnit.v5_periodic_entire_descends
