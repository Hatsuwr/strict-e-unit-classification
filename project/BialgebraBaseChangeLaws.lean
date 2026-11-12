import TypedMorphismMaps
import BialgebraBaseChangeCounit

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
variable {k H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]
variable (A : Type*) [CommRing A] [Algebra k A]

def baseChangeTripleEquiv :
    (A ⊗[k] H) ⊗[A] ((A ⊗[k] H) ⊗[A] (A ⊗[k] H)) ≃ₐ[A]
      A ⊗[k] (H ⊗[k] (H ⊗[k] H)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A ⊗[k] H))
    (algebraTensorBaseChangeEquiv (k:=k) A H H)).trans
      (algebraTensorBaseChangeEquiv (k:=k) A H (H ⊗[k] H))

@[simp] theorem baseChangeTripleEquiv_tmul (a b c : A) (h i j : H) :
    baseChangeTripleEquiv (k:=k) (H:=H) A
      ((a ⊗ₜ[k] h) ⊗ₜ[A] ((b ⊗ₜ[k] i) ⊗ₜ[A] (c ⊗ₜ[k] j))) =
      (a * (b*c)) ⊗ₜ[k] (h ⊗ₜ[k] (i ⊗ₜ[k] j)) := by
  simp [baseChangeTripleEquiv]

 theorem baseChangeTriple_right (a b : A) (h : H) (z : H ⊗[k] H) :
    baseChangeTripleEquiv (k:=k) (H:=H) A
      ((a ⊗ₜ[k] h) ⊗ₜ[A]
        (algebraTensorBaseChangeEquiv (k:=k) A H H).symm (b ⊗ₜ[k] z)) =
      (a*b) ⊗ₜ[k] (h ⊗ₜ[k] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, zero_tmul, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul i j => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

 theorem baseChangeTriple_left (a b : A) (z : H ⊗[k] H) (h : H) :
    baseChangeTripleEquiv (k:=k) (H:=H) A
      (Algebra.TensorProduct.assoc A (A ⊗[k] H) (A ⊗[k] H) (A ⊗[k] H)
        ((algebraTensorBaseChangeEquiv (k:=k) A H H).symm (a ⊗ₜ[k] z) ⊗ₜ[A]
          (b ⊗ₜ[k] h))) =
      (a*b) ⊗ₜ[k] (Algebra.TensorProduct.assoc k H H H (z ⊗ₜ[k] h)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, zero_tmul, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul i j => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, TensorProduct.add_tmul,
      TypedMaps.algEquiv_add, TypedMaps.algHom_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

theorem baseChange_comul_right_leg (a : A) (z : H ⊗[k] H) :
    baseChangeTripleEquiv (k:=k) (H:=H) A
      (Algebra.TensorProduct.map (AlgHom.id A (A ⊗[k] H)) (baseChangeComul (k:=k) (H:=H) A)
        ((algebraTensorBaseChangeEquiv (k:=k) A H H).symm (a ⊗ₜ[k] z))) =
      a ⊗ₜ[k] ((Coalgebra.comul (R:=k)).lTensor H z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, zero_tmul, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul h i =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeComul_tmul,
      baseChangeTriple_right, mul_one, LinearMap.lTensor_tmul]
  | add x y hx hy => simp only [TensorProduct.tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

theorem baseChange_comul_left_leg (a : A) (z : H ⊗[k] H) :
    baseChangeTripleEquiv (k:=k) (H:=H) A
      (Algebra.TensorProduct.assoc A (A ⊗[k] H) (A ⊗[k] H) (A ⊗[k] H)
        (Algebra.TensorProduct.map (baseChangeComul (k:=k) (H:=H) A) (AlgHom.id A (A ⊗[k] H))
          ((algebraTensorBaseChangeEquiv (k:=k) A H H).symm (a ⊗ₜ[k] z)))) =
      a ⊗ₜ[k] (TensorProduct.assoc k H H H ((Coalgebra.comul (R:=k)).rTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, zero_tmul, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul h i =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeComul_tmul,
      baseChangeTriple_left, mul_one, LinearMap.rTensor_tmul]
    rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

/-- Coassociativity of scalar extension follows from the original coalgebra law. -/
theorem baseChangeComul_coassoc :
    (Algebra.TensorProduct.assoc A (A ⊗[k] H) (A ⊗[k] H) (A ⊗[k] H)).toAlgHom.comp
      ((Algebra.TensorProduct.map (baseChangeComul (k:=k) (H:=H) A) (AlgHom.id A (A ⊗[k] H))).comp
        (baseChangeComul (k:=k) (H:=H) A)) =
      (Algebra.TensorProduct.map (AlgHom.id A (A ⊗[k] H)) (baseChangeComul (k:=k) (H:=H) A)).comp
        (baseChangeComul (k:=k) (H:=H) A) := by
  ext h
  apply (baseChangeTripleEquiv (k:=k) (H:=H) A).injective
  change baseChangeTripleEquiv (k:=k) (H:=H) A
      (Algebra.TensorProduct.assoc A _ _ _
        (Algebra.TensorProduct.map (baseChangeComul (k:=k) (H:=H) A) (AlgHom.id A _)
          ((algebraTensorBaseChangeEquiv (k:=k) A H H).symm ((1:A) ⊗ₜ[k] Coalgebra.comul h)))) =
    baseChangeTripleEquiv (k:=k) (H:=H) A
      (Algebra.TensorProduct.map (AlgHom.id A _) (baseChangeComul (k:=k) (H:=H) A)
        ((algebraTensorBaseChangeEquiv (k:=k) A H H).symm ((1:A) ⊗ₜ[k] Coalgebra.comul h)))
  rw [baseChange_comul_left_leg, baseChange_comul_right_leg, Coalgebra.coassoc_apply]

/-- The scalar-extended bialgebra, constructed from the proven laws.
This is a named construction, not a globally installed instance. -/
def baseChangeBialgebra : Bialgebra A (A ⊗[k] H) :=
  Bialgebra.ofAlgHom (baseChangeComul (k:=k) (H:=H) A)
    (baseChangeCounit (k:=k) (H:=H) A)
    (baseChangeComul_coassoc A) (baseChangeCounit_left A) (baseChangeCounit_right A)

/-- An original grouplike unit becomes a grouplike unit for the constructed
scalar-extended bialgebra, via the actual inclusion of the right factor. -/
theorem baseChange_grouplike_unit (χ : Hˣ)
    (hχ : Coalgebra.comul (R:=k) (χ:H) = (χ:H) ⊗ₜ[k] (χ:H)) :
    letI := baseChangeBialgebra (k:=k) (H:=H) A
    let u := Units.map
      (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H).toMonoidHom χ
    Coalgebra.comul (R:=A) (u : A ⊗[k] H) =
      (u : A ⊗[k] H) ⊗ₜ[A] (u : A ⊗[k] H) := by
  letI := baseChangeBialgebra (k:=k) (H:=H) A
  change baseChangeComul (k:=k) (H:=H) A ((1:A) ⊗ₜ[k] (χ:H)) =
    ((1:A) ⊗ₜ[k] (χ:H)) ⊗ₜ[A] ((1:A) ⊗ₜ[k] (χ:H))
  rw [baseChangeComul_tmul, hχ, algebraTensorBaseChangeEquiv_symm_tmul]

#print axioms baseChangeTripleEquiv
#print axioms baseChangeTripleEquiv_tmul
#print axioms baseChangeTriple_right
#print axioms baseChangeTriple_left
#print axioms baseChange_comul_right_leg
#print axioms baseChange_comul_left_leg
#print axioms baseChangeComul_coassoc
#print axioms baseChangeBialgebra
#print axioms baseChange_grouplike_unit
end StrictEUnit
