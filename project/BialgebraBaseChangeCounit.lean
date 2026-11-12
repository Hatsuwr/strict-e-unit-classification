import TypedMorphismMaps
import BialgebraBaseChange
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option synthInstance.maxHeartbeats 20000
set_option maxHeartbeats 200000
namespace StrictEUnit
variable {k H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]
variable (A : Type*) [CommRing A] [Algebra k A]
/-- Left counit contraction commutes with scalar extension. -/
theorem baseChangeCounit_contract_left (z : H ⊗[k] H) :
    (TensorProduct.lid A (A ⊗[k] H))
      ((Algebra.TensorProduct.map (baseChangeCounit A)
        (AlgHom.id A (A ⊗[k] H)))
        ((algebraTensorBaseChangeEquiv (k := k) A H H).symm
          ((1 : A) ⊗ₜ[k] z))) =
    (1 : A) ⊗ₜ[k] (TensorProduct.lid k H)
      (((Coalgebra.counit (R := k)).rTensor H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul m n =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul,
      Algebra.TensorProduct.map_tmul, baseChangeCounit_tmul, one_mul,
      AlgHom.id_apply, TensorProduct.lid_tmul, LinearMap.rTensor_tmul]
    rw [smul_tmul', smul_eq_mul, mul_one]
    rw [show algebraMap k A (Coalgebra.counit (R := k) m) =
      Coalgebra.counit (R := k) m • (1 : A) by simp [Algebra.smul_def]]
    rw [TensorProduct.smul_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]



/-- Right counit contraction commutes with scalar extension. -/
theorem baseChangeCounit_contract_right (z : H ⊗[k] H) :
    (TensorProduct.rid A (A ⊗[k] H))
      ((Algebra.TensorProduct.map (AlgHom.id A (A ⊗[k] H))
        (baseChangeCounit A))
        ((algebraTensorBaseChangeEquiv (k := k) A H H).symm
          ((1 : A) ⊗ₜ[k] z))) =
    (1 : A) ⊗ₜ[k] (TensorProduct.rid k H)
      (((Coalgebra.counit (R := k)).lTensor H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul m n =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul,
      Algebra.TensorProduct.map_tmul, baseChangeCounit_tmul, one_mul,
      AlgHom.id_apply, TensorProduct.rid_tmul, LinearMap.lTensor_tmul]
    rw [smul_tmul', smul_eq_mul, mul_one]
    rw [show algebraMap k A (Coalgebra.counit (R := k) n) =
      Coalgebra.counit (R := k) n • (1 : A) by simp [Algebra.smul_def]]
    rw [TensorProduct.smul_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

theorem baseChangeCounit_left :
    (Algebra.TensorProduct.map (baseChangeCounit A)
      (AlgHom.id A (A ⊗[k] H))).comp (baseChangeComul A) =
    (Algebra.TensorProduct.lid A (A ⊗[k] H)).symm.toAlgHom := by
  ext h
  apply (TensorProduct.lid A (A ⊗[k] H)).injective
  change (TensorProduct.lid A (A ⊗[k] H))
    ((Algebra.TensorProduct.map (baseChangeCounit A)
      (AlgHom.id A (A ⊗[k] H)))
      ((algebraTensorBaseChangeEquiv (k := k) A H H).symm
        ((1 : A) ⊗ₜ[k] Coalgebra.comul (R := k) h))) = _
  rw [baseChangeCounit_contract_left, Coalgebra.rTensor_counit_comul]
  simp

theorem baseChangeCounit_right :
    (Algebra.TensorProduct.map (AlgHom.id A (A ⊗[k] H))
      (baseChangeCounit A)).comp (baseChangeComul A) =
    (Algebra.TensorProduct.rid A A (A ⊗[k] H)).symm.toAlgHom := by
  ext h
  apply (TensorProduct.rid A (A ⊗[k] H)).injective
  change (TensorProduct.rid A (A ⊗[k] H))
    ((Algebra.TensorProduct.map (AlgHom.id A (A ⊗[k] H))
      (baseChangeCounit A))
      ((algebraTensorBaseChangeEquiv (k := k) A H H).symm
        ((1 : A) ⊗ₜ[k] Coalgebra.comul (R := k) h))) = _
  rw [baseChangeCounit_contract_right, Coalgebra.lTensor_counit_comul]
  simp
end StrictEUnit
#print axioms StrictEUnit.baseChangeCounit_contract_left


#print axioms StrictEUnit.baseChangeCounit_contract_right
#print axioms StrictEUnit.baseChangeCounit_left
#print axioms StrictEUnit.baseChangeCounit_right
