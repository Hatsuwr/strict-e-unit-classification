import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! The coefficient-extended right regular coaction has exactly scalar
invariants. This is one local calculation for component descent, not a
construction of components, a finite étale cover, or Kummer coordinates. -/
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k R H : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [CommRing H] [Bialgebra k H]

/-- Counit evaluation on the group factor, retaining the coefficient ring. -/
def v5ComponentEval : R ⊗[k] H →ₗ[k] R :=
  (TensorProduct.rid k R).toLinearMap.comp
    ((Coalgebra.counit (R := k) (A := H)).lTensor R)

@[simp] theorem v5ComponentEval_tmul (r : R) (h : H) :
    v5ComponentEval (r ⊗ₜ[k] h) = Coalgebra.counit (R := k) h • r := rfl

/-- Contract the first group slot of the regular coaction. -/
theorem v5Component_contract_comul (x : R ⊗[k] H) :
    ((TensorProduct.lid k H).toLinearMap.comp
      ((Coalgebra.counit (R := k) (A := H)).rTensor H)).lTensor R
      ((Coalgebra.comul (R := k) (A := H)).lTensor R x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r h =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply,
      Coalgebra.rTensor_counit_comul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]

/-- The same contraction of the trivial coaction is the scalar projection. -/
theorem v5Component_contract_trivial (x : R ⊗[k] H) :
    ((TensorProduct.lid k H).toLinearMap.comp
      ((Coalgebra.counit (R := k) (A := H)).rTensor H)).lTensor R
      (((TensorProduct.mk k H H).flip 1).lTensor R x) =
    v5ComponentEval x ⊗ₜ[k] (1 : H) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [v5ComponentEval]
  | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
  | tmul r h =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply,
      LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, v5ComponentEval_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- Fixed functions on each translated connected component are constants
in the coefficient ring. No rational-point detection or averaging is used. -/
theorem v5Component_regular_invariant_iff (x : R ⊗[k] H) :
    (Coalgebra.comul (R := k) (A := H)).lTensor R x =
      ((TensorProduct.mk k H H).flip 1).lTensor R x ↔
    ∃ r : R, x = r ⊗ₜ[k] (1 : H) := by
  constructor
  · intro hx
    refine ⟨v5ComponentEval x, ?_⟩
    have he := congrArg
      (((TensorProduct.lid k H).toLinearMap.comp
        ((Coalgebra.counit (R := k) (A := H)).rTensor H)).lTensor R) hx
    simpa only [v5Component_contract_comul, v5Component_contract_trivial] using he
  · rintro ⟨r, rfl⟩
    simp only [LinearMap.lTensor_tmul, LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [show Coalgebra.comul (R := k) (1 : H) = 1 ⊗ₜ[k] 1 from
      (Bialgebra.comulAlgHom k H).map_one]

/-- Componentwise application gives precisely a family of scalars. The
component index set may be arbitrary; geometric finiteness is a separate input. -/
theorem v5Component_product_regular_invariant_iff {J : Type*}
    (x : J → R ⊗[k] H) :
    (∀ j, (Coalgebra.comul (R := k) (A := H)).lTensor R (x j) =
      ((TensorProduct.mk k H H).flip 1).lTensor R (x j)) ↔
    ∃ r : J → R, ∀ j, x j = r j ⊗ₜ[k] (1 : H) := by
  constructor
  · intro hx
    refine ⟨fun j => v5ComponentEval (x j), ?_⟩
    intro j
    obtain ⟨r, hr⟩ := (v5Component_regular_invariant_iff (x j)).mp (hx j)
    change x j = v5ComponentEval (x j) ⊗ₜ[k] (1 : H)
    rw [hr, v5ComponentEval_tmul]
    have hc : Coalgebra.counit (R := k) (1 : H) = 1 :=
      (Bialgebra.counitAlgHom k H).map_one
    rw [hc, one_smul]
  · rintro ⟨r, hr⟩ j
    exact (v5Component_regular_invariant_iff (x j)).mpr ⟨r j, hr j⟩

end StrictEUnit
#print axioms StrictEUnit.v5Component_regular_invariant_iff
#print axioms StrictEUnit.v5Component_contract_comul
#print axioms StrictEUnit.v5Component_contract_trivial

#print axioms StrictEUnit.v5Component_product_regular_invariant_iff
