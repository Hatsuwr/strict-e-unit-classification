import V5WideSolutionFiber
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

/-- The coordinate on the punctured line, as an actual unit of the generated
solution algebra. Its inverse is the other base generator. -/
def v5WideSolutionCoordinate {ι : Type} (f : ι → entireFunctionAlgebra) :
    (v5WideSolutionAlgebra f)ˣ where
  val := v5WideSolutionParameter f true
  inv := v5WideSolutionParameter f false
  val_inv := by
    apply Subtype.ext
    funext z
    change (z : ℂ) * (↑z⁻¹ : ℂ) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := by
    apply Subtype.ext
    funext z
    change (↑z⁻¹ : ℂ) * (z : ℂ) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- The actual Laurent base of the chosen solution algebra, not a field of
coefficients with unrestricted poles at the ordinary point. -/
def v5WideSolutionBase {ι : Type} (f : ι → entireFunctionAlgebra) :
    LaurentPolynomial AlgebraicComplex →ₐ[AlgebraicComplex] v5WideSolutionAlgebra f where
  __ := LaurentPolynomial.eval₂ (algebraMap _ _) (v5WideSolutionCoordinate f)
  commutes' c := LaurentPolynomial.eval₂_C _ _ c

@[simp] theorem v5WideSolutionBase_apply {ι : Type} (f : ι → entireFunctionAlgebra)
    (P : LaurentPolynomial AlgebraicComplex) (z : ℂˣ) :
    (v5WideSolutionBase f P).val z = arithmeticLaurentEvaluation z P := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, Subalgebra.coe_add, Pi.add_apply, hp, hq]
  | C_mul_T n c =>
      rw [map_mul, map_mul]
      change ((LaurentPolynomial.eval₂ (algebraMap _ _) (v5WideSolutionCoordinate f) (LaurentPolynomial.C c)).val z) *
          ((LaurentPolynomial.eval₂ (algebraMap _ _) (v5WideSolutionCoordinate f) (LaurentPolynomial.T n)).val z) =
        LaurentPolynomial.eval₂ _ z (LaurentPolynomial.C c) *
          LaurentPolynomial.eval₂ _ z (LaurentPolynomial.T n)
      simp only [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
      change (c : ℂ) * ((Units.map (Pi.evalRingHom (fun _ : ℂˣ => ℂ) z)
        (Units.map (v5WideSolutionAlgebra f).val.toMonoidHom
          (v5WideSolutionCoordinate f ^ n)) : ℂˣ) : ℂ) =
        (c : ℂ) * ((z ^ n : ℂˣ) : ℂ)
      rw [map_zpow, map_zpow]
      rfl

theorem v5WideSolutionBase_injective {ι : Type} (f : ι → entireFunctionAlgebra) :
    Function.Injective (v5WideSolutionBase f) := by
  apply (injective_iff_map_eq_zero (v5WideSolutionBase f)).mpr
  intro P hP
  induction P using LaurentPolynomial.induction_on_mul_T with
  | Qf =>
    rename_i p n
    have hvals (z : ℂˣ) := congrArg (fun r : v5WideSolutionAlgebra f => r.val z) hP
    have hpvals (z : ℂˣ) :
        Polynomial.eval (z : ℂ) (p.map (algebraicClosure ℚ ℂ).val.toRingHom) = 0 := by
      have h := hvals z
      change (v5WideSolutionBase f (p.toLaurent * LaurentPolynomial.T (-(n : ℤ)))).val z = 0 at h
      rw [v5WideSolutionBase_apply] at h
      simp only [arithmeticLaurentEvaluation, map_mul, LaurentPolynomial.eval₂_toLaurent,
        LaurentPolynomial.eval₂_T_neg_n] at h
      rw [Polynomial.eval_map]
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (Units.ne_zero z⁻¹))
    have hp : p.map (algebraicClosure ℚ ℂ).val.toRingHom = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hinf : Set.Infinite ({0}ᶜ : Set ℂ) := (Set.finite_singleton _).infinite_compl
      apply hinf.mono
      intro z hz
      exact hpvals (Units.mk0 z (by simpa using hz))
    rw [(Polynomial.map_injective (algebraicClosure ℚ ℂ).val.toRingHom Subtype.val_injective) (hp.trans (Polynomial.map_zero _).symm),
      map_zero, zero_mul]

end StrictEUnit

#print axioms StrictEUnit.v5WideSolutionBase_apply
#print axioms StrictEUnit.v5WideSolutionBase_injective
