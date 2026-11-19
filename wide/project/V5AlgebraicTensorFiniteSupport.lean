import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Defs

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {F L D : Type*} [Field F] [Field L] [CommRing D] [Algebra F L] [Algebra F D]

private def tensorSubfieldMap (U : IntermediateField F L) : U ⊗[F] D →ₐ[F] L ⊗[F] D :=
  Algebra.TensorProduct.map U.val (AlgHom.id F D)

private theorem tensorSubfieldMap_injective (U : IntermediateField F L) :
    Function.Injective (tensorSubfieldMap (D := D) U) :=
  Module.Flat.rTensor_preserves_injective_linearMap U.val.toLinearMap Subtype.val_injective

private theorem tensorSubfieldMap_inclusion (U V : IntermediateField F L) (hUV : U ≤ V)
    (x : U ⊗[F] D) :
    tensorSubfieldMap V (Algebra.TensorProduct.map (IntermediateField.inclusion hUV)
      (AlgHom.id F D) x) = tensorSubfieldMap U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Each tensor in an algebraic field extension comes from a finite
intermediate field on the algebraic side. No finite-type hypothesis on D. -/
theorem v5_algebraicTensor_finiteSupport [Algebra.IsAlgebraic F L] (x : L ⊗[F] D) :
    ∃ U : IntermediateField F L, FiniteDimensional F U ∧
      ∃ y : U ⊗[F] D, tensorSubfieldMap U y = x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    exact ⟨⊥, inferInstance, 0, map_zero _⟩
  | tmul a b =>
    let U := IntermediateField.adjoin F {a}
    have ha : a ∈ U := IntermediateField.subset_adjoin F {a} (by simp)
    have ha' : IsIntegral F a := isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic a)
    exact ⟨U, IntermediateField.adjoin.finiteDimensional ha', (⟨a, ha⟩ : U) ⊗ₜ[F] b, rfl⟩
  | add a b ha hb =>
    obtain ⟨U, hU, y, hy⟩ := ha
    obtain ⟨V, hV, z, hz⟩ := hb
    letI := hU
    letI := hV
    let W : IntermediateField F L := U ⊔ V
    let i : U →ₐ[F] W := IntermediateField.inclusion le_sup_left
    let j : V →ₐ[F] W := IntermediateField.inclusion le_sup_right
    refine ⟨W, IntermediateField.finiteDimensional_sup U V,
      Algebra.TensorProduct.map i (AlgHom.id F D) y +
        Algebra.TensorProduct.map j (AlgHom.id F D) z, ?_⟩
    rw [map_add,
      tensorSubfieldMap_inclusion U W le_sup_left y,
      tensorSubfieldMap_inclusion V W le_sup_right z, hy, hz]

/-- Reducedness for finite intermediate tensors upgrades to any algebraic
extension by finite support and flat tensor inclusion over the field. -/
theorem v5_reducedTensor_of_finiteSubfields [Algebra.IsAlgebraic F L]
    (h : ∀ U : IntermediateField F L, FiniteDimensional F U → IsReduced (U ⊗[F] D)) :
    IsReduced (L ⊗[F] D) := by
  constructor
  intro x hx
  obtain ⟨U, hU, y, rfl⟩ := v5_algebraicTensor_finiteSupport x
  letI := h U hU
  have hi := tensorSubfieldMap_injective (D := D) U
  obtain ⟨n, hn⟩ := hx
  let m := (tensorSubfieldMap (D := D) U).toRingHom
  have hpow : m (y ^ n) = m y ^ n := m.map_pow y n
  have hny : m y ^ n = 0 := hn
  have hzero : m 0 = 0 := m.map_zero
  have hy : IsNilpotent y := ⟨n, hi (hpow.trans (hny.trans hzero.symm))⟩
  calc
    tensorSubfieldMap U y = tensorSubfieldMap U 0 := congrArg _ hy.eq_zero
    _ = 0 := m.map_zero

end StrictEUnit
#print axioms StrictEUnit.v5_algebraicTensor_finiteSupport
#print axioms StrictEUnit.v5_reducedTensor_of_finiteSubfields
