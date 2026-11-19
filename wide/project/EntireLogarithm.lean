import EntirePrimitive
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A normalized entire logarithm of an actual zero-free entire function.
The primitive is constructed by the previously checked entire series, not assumed. -/
noncomputable section
namespace StrictEUnit

/-- Every zero-free entire function has a normalized entire logarithm relative
to its value at zero, with the actual logarithmic derivative. -/
theorem exists_normalized_entire_logarithm {w : ℂ → ℂ}
    (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0) :
    ∃ g : ℂ → ℂ, g 0 = 0 ∧ Differentiable ℂ g ∧
      (∀ z, HasDerivAt g (deriv w z / w z) z) ∧
      ∀ z, w z = w 0 * Complex.exp (g z) := by
  have hd : Differentiable ℂ (deriv w) :=
    differentiableOn_univ.mp (hw.differentiableOn.deriv isOpen_univ)
  obtain ⟨g,hg0,hg,hgd⟩ := exists_entire_primitive (hd.div hw hnz)
  refine ⟨g,hg0,hg,hgd,?_⟩
  have hp : ∀ z, HasDerivAt (fun x => w x * Complex.exp (-g x)) 0 z := by
    intro z
    convert (hw z).hasDerivAt.mul ((hgd z).neg.cexp) using 1
    field_simp [hnz z]
    ring
  have hc := is_const_of_deriv_eq_zero
    (fun z => (hp z).differentiableAt) (fun z => (hp z).deriv)
  intro z
  have he : w z * Complex.exp (-g z) = w 0 := by
    simpa [hg0] using hc z 0
  have he' := congrArg (fun x : ℂ => x * Complex.exp (g z)) he
  simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] using he'
end StrictEUnit
#print axioms StrictEUnit.exists_normalized_entire_logarithm
