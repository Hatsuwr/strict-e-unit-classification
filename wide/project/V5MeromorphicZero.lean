import EntireTaylorEmbedding
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
namespace StrictEUnit

/-- A punctured function with at worst a pole at the deleted origin.
Multiplying by a nonnegative integral power yields a genuine entire function. -/
def V5MeromorphicZero (f : ℂˣ → ℂ) : Prop :=
  ∃ (n : ℕ) (F : ℂ → ℂ), Differentiable ℂ F ∧ ∀ z : ℂˣ, F z = (z : ℂ)^n * f z

theorem V5MeromorphicZero.of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    V5MeromorphicZero (fun z => F z) :=
  ⟨0, F, hF, fun z => by rw [pow_zero, one_mul]⟩

theorem V5MeromorphicZero.add {f g : ℂˣ → ℂ}
    (hf : V5MeromorphicZero f) (hg : V5MeromorphicZero g) : V5MeromorphicZero (f + g) := by
  obtain ⟨n,F,hF,eF⟩ := hf
  obtain ⟨m,G,hG,eG⟩ := hg
  refine ⟨n+m, fun z => z^m * F z + z^n * G z,
    ((differentiable_id.pow m).mul hF).add ((differentiable_id.pow n).mul hG), ?_⟩
  intro z
  change (z : ℂ)^m * F z + (z : ℂ)^n * G z = (z : ℂ)^(n+m)*(f z+g z)
  rw [eF, eG, pow_add, mul_add]
  ring

theorem V5MeromorphicZero.mul {f g : ℂˣ → ℂ}
    (hf : V5MeromorphicZero f) (hg : V5MeromorphicZero g) : V5MeromorphicZero (f * g) := by
  obtain ⟨n,F,hF,eF⟩ := hf
  obtain ⟨m,G,hG,eG⟩ := hg
  refine ⟨n+m, fun z => F z * G z, hF.mul hG, ?_⟩
  intro z
  change F z * G z = (z : ℂ)^(n+m)*(f z*g z)
  rw [eF, eG, pow_add]
  ring

theorem V5MeromorphicZero.invCoord :
    V5MeromorphicZero (fun z : ℂˣ => (↑z⁻¹ : ℂ)) := by
  refine ⟨1, fun _ => 1, differentiable_const _, ?_⟩
  intro z
  simp [Units.val_inv_eq_inv_val, Units.ne_zero z]

theorem V5MeromorphicZero.pullback {f : ℂˣ → ℂ} (h : V5MeromorphicZero f) (q : ℕ) :
    V5MeromorphicZero (fun z => f (z^q)) := by
  obtain ⟨n,F,hF,eF⟩ := h
  refine ⟨q*n, fun z => F (z^q), hF.comp (differentiable_id.pow q), ?_⟩
  intro z
  simpa only [Units.val_pow_eq_pow_val, pow_mul] using eF (z^q)

def v5MeromorphicZeroAlgebra (k : Type*) [CommRing k] [Algebra k ℂ] :
    Subalgebra k (ℂˣ → ℂ) where
  carrier := {f | V5MeromorphicZero f}
  zero_mem' := V5MeromorphicZero.of_entire (differentiable_const 0)
  one_mem' := V5MeromorphicZero.of_entire (differentiable_const 1)
  add_mem' := V5MeromorphicZero.add
  mul_mem' := V5MeromorphicZero.mul
  algebraMap_mem' a := V5MeromorphicZero.of_entire (differentiable_const (algebraMap k ℂ a))

variable (k : Type*) [CommRing k] [Algebra k ℂ]

def v5MeromorphicZeroCoordinate : (v5MeromorphicZeroAlgebra k)ˣ where
  val := ⟨fun z => z.val, V5MeromorphicZero.of_entire differentiable_id⟩
  inv := ⟨fun z => (↑z⁻¹ : ℂ), V5MeromorphicZero.invCoord⟩
  val_inv := by
    apply Subtype.ext
    funext z
    change (z : ℂ) * (↑z⁻¹ : ℂ) = 1
    simp [Units.val_inv_eq_inv_val, Units.ne_zero z]
  inv_val := by
    apply Subtype.ext
    funext z
    change (↑z⁻¹ : ℂ) * (z : ℂ) = 1
    simp [Units.val_inv_eq_inv_val, Units.ne_zero z]

def v5MeromorphicZeroLaurent : LaurentPolynomial k →ₐ[k] v5MeromorphicZeroAlgebra k where
  __ := LaurentPolynomial.eval₂ (algebraMap k _) (v5MeromorphicZeroCoordinate k)
  commutes' := LaurentPolynomial.eval₂_C _ _

theorem v5MeromorphicZeroLaurent_apply (x : LaurentPolynomial k) (z : ℂˣ) :
    (v5MeromorphicZeroLaurent k x).val z = LaurentPolynomial.eval₂ (algebraMap k ℂ) z x := by
  let ev : v5MeromorphicZeroAlgebra k →+* ℂ :=
    { toFun := fun x => x.val z, map_one' := rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
  induction x using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    change ev ((v5MeromorphicZeroLaurent k).toRingHom (a+b)) = _
    rw [(v5MeromorphicZeroLaurent k).map_add, ev.map_add, (LaurentPolynomial.eval₂ (algebraMap k ℂ) z).map_add]
    exact congrArg₂ (· + ·) ha hb
  | C_mul_T n a =>
    change ev (LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C a * LaurentPolynomial.T n)) = _
    rw [LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, ev.map_mul]
    change algebraMap k ℂ a * (Units.map ev.toMonoidHom (v5MeromorphicZeroCoordinate k ^ n)).val = _
    have hu : Units.map ev.toMonoidHom (v5MeromorphicZeroCoordinate k) = z := Units.ext rfl
    rw [map_zpow, hu]

end StrictEUnit
#print axioms StrictEUnit.V5MeromorphicZero.add
#print axioms StrictEUnit.V5MeromorphicZero.mul
#print axioms StrictEUnit.V5MeromorphicZero.pullback
#print axioms StrictEUnit.v5MeromorphicZeroLaurent_apply
