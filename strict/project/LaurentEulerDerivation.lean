import LaurentEulerConstants
import Mathlib.RingTheory.Derivation.Basic

/-! The actual Euler operator is a derivation; Leibniz is proved from the
finite Hahn-series coefficient convolution, without assuming differentiability. -/
noncomputable section
set_option maxHeartbeats 200000
open HahnSeries Finset
open scoped BigOperators
namespace StrictEUnit
variable {k : Type*} [Field k]

theorem laurentEuler_support_subset (f : LaurentSeries k) :
    (laurentEuler f).support ⊆ f.support := by
  intro n hn
  simp only [mem_support, laurentEuler_coeff, ne_eq] at hn ⊢
  exact fun h => hn (by rw [h, mul_zero])

/-- Leibniz for t d/dt, proved coefficientwise on the finite convolution. -/
theorem laurentEuler_mul (f g : LaurentSeries k) :
    laurentEuler (f*g) = laurentEuler f * g + f * laurentEuler g := by
  ext n
  rw [laurentEuler_coeff, coeff_add, coeff_mul,
    coeff_mul_left' f.isPWO_support (laurentEuler_support_subset f),
    coeff_mul_right' g.isPWO_support (laurentEuler_support_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := (mem_addAntidiagonal.mp hij).2.2
  rw [laurentEuler_coeff, laurentEuler_coeff, ← hn, Int.cast_add]
  ring

/-- The Euler operator as a linear map for coefficientwise scalar multiplication. -/
def laurentEulerLinear : LaurentSeries k →ₗ[k] LaurentSeries k :=
  { toFun := laurentEuler
    map_add' := fun f g => by
      ext n
      simp only [laurentEuler_coeff, coeff_add]
      ring
    map_smul' := fun c f => by
      ext n
      simp only [laurentEuler_coeff, coeff_smul, Pi.smul_apply, RingHom.id_apply,
        smul_eq_mul]
      ring }

@[simp] theorem laurentEulerLinear_apply (f : LaurentSeries k) :
    laurentEulerLinear f = laurentEuler f := rfl

/-- A bundled derivation on the actual Laurent-series field. -/
def laurentEulerDerivation : Derivation k (LaurentSeries k) (LaurentSeries k) :=
  { toFun := laurentEuler
    map_add' := fun f g => by
      ext n
      simp only [laurentEuler_coeff, coeff_add]
      ring
    map_smul' := fun c f => by
      ext n
      change (laurentEuler (algebraMap k (LaurentSeries k) c * f)).coeff n = _
      simp only [laurentEuler_coeff, coeff_smul, Pi.smul_apply, RingHom.id_apply,
        smul_eq_mul]
      rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
      change (n:k) * (single (0:ℤ) c * f).coeff n = _
      rw [show n = n + 0 by omega, coeff_single_mul_add]
      simp only [add_zero]
      ring
    map_one_eq_zero' := by
      change laurentEuler (1 : LaurentSeries k) = 0
      ext n
      simp only [laurentEuler_coeff, coeff_one, coeff_zero]
      split_ifs with h
      · subst n; simp
      · simp
    leibniz' := fun f g => by
      change laurentEuler (f*g) = f * laurentEuler g + g * laurentEuler f
      rw [laurentEuler_mul]
      ring }


@[simp] theorem laurentEulerDerivation_apply (f : LaurentSeries k) :
    laurentEulerDerivation f = laurentEuler f := rfl

#print axioms laurentEuler_support_subset
#print axioms laurentEuler_mul
#print axioms laurentEulerLinear
#print axioms laurentEulerLinear_apply
#print axioms laurentEulerDerivation
#print axioms laurentEulerDerivation_apply
end StrictEUnit
