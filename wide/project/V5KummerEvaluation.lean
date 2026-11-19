import V5PeriodicExpDescent
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
namespace StrictEUnit

/-- The pointwise unit w ↦ exp(w/q). -/
def v5KummerUnit (q : ℕ) : (ℂ → ℂ)ˣ where
  val w := Complex.exp (w / (q : ℂ))
  inv w := Complex.exp (-(w / (q : ℂ)))
  val_inv := by funext w; change Complex.exp _ * Complex.exp _ = 1
                rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by funext w; change Complex.exp _ * Complex.exp _ = 1
                rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

def v5KummerPoint (q : ℕ) (w : ℂ) : ℂˣ :=
  Units.map (Pi.evalRingHom (fun _ : ℂ => ℂ) w).toMonoidHom (v5KummerUnit q)

@[simp] theorem v5KummerPoint_val (q : ℕ) (w : ℂ) :
    (v5KummerPoint q w : ℂ) = Complex.exp (w / (q : ℂ)) := rfl

theorem v5KummerPoint_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (v5KummerPoint q) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  intro t
  refine ⟨(q : ℂ) * Complex.log (t : ℂ), Units.ext ?_⟩
  rw [v5KummerPoint_val, mul_comm, mul_div_cancel_right₀ _ hq', Complex.exp_log (Units.ne_zero t)]

def v5KummerEval {k : Type*} [CommRing k] (ι : k →+* ℂ) (q : ℕ) :
    LaurentPolynomial k →+* (ℂ → ℂ) :=
  LaurentPolynomial.eval₂ (Pi.ringHom (fun _ : ℂ => ι)) (v5KummerUnit q)

@[simp] theorem v5KummerEval_apply {k : Type*} [CommRing k]
    (ι : k →+* ℂ) (q : ℕ) (p : LaurentPolynomial k) (w : ℂ) :
    v5KummerEval ι q p w = LaurentPolynomial.eval₂ ι (v5KummerPoint q w) p := by
  let ev := Pi.evalRingHom (fun _ : ℂ => ℂ) w
  change ev (v5KummerEval ι q p) = _
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n a =>
    simp only [v5KummerEval, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
    change ι a * ev ((v5KummerUnit q ^ n : (ℂ → ℂ)ˣ) : ℂ → ℂ) = _
    rw [show ev ((v5KummerUnit q ^ n : (ℂ → ℂ)ˣ) : ℂ → ℂ) =
      ((Units.map ev.toMonoidHom (v5KummerUnit q ^ n) : ℂˣ) : ℂ) from rfl, map_zpow]
    rfl

/-- Evaluation on all units separates Laurent polynomials over a subfield. -/
theorem v5_laurent_eq_zero_of_eval_units {k : Type*} [Field k]
    (ι : k →+* ℂ) (p : LaurentPolynomial k)
    (h : ∀ t : ℂˣ, LaurentPolynomial.eval₂ ι t p = 0) : p = 0 := by
  induction p using LaurentPolynomial.induction_on_mul_T with
  | @Qf P n =>
    have hz (t : ℂˣ) : (P.map ι).IsRoot (t : ℂ) := by
      have he := h t
      simp only [map_mul, LaurentPolynomial.eval₂_toLaurent,
        LaurentPolynomial.eval₂_T_neg_n] at he
      exact (Polynomial.eval_map ι _).trans
        ((mul_eq_zero.mp he).resolve_right (pow_ne_zero _ (Units.ne_zero t⁻¹)))
    have hinf : Set.Infinite {x : ℂ | (P.map ι).IsRoot x} := by
      apply (Set.infinite_univ.diff (Set.finite_singleton (0 : ℂ))).mono
      intro x hx
      have hx0 : x ≠ 0 := hx.2
      exact hz (Units.mk0 x hx0)
    have hP : P = 0 := Polynomial.map_eq_zero_iff ι.injective |>.mp
      (Polynomial.eq_zero_of_infinite_isRoot _ hinf)
    simp [hP]

theorem v5KummerEval_injective {k : Type*} [Field k] (ι : k →+* ℂ)
    (q : ℕ) (hq : 0 < q) : Function.Injective (v5KummerEval ι q) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply v5_laurent_eq_zero_of_eval_units ι
  intro t
  obtain ⟨w, rfl⟩ := v5KummerPoint_surjective q hq t
  rw [← v5KummerEval_apply, map_sub, hab, sub_self]
  rfl

end StrictEUnit
#print axioms StrictEUnit.v5KummerUnit
#print axioms StrictEUnit.v5KummerPoint_surjective
#print axioms StrictEUnit.v5KummerEval_apply
#print axioms StrictEUnit.v5_laurent_eq_zero_of_eval_units
#print axioms StrictEUnit.v5KummerEval_injective
