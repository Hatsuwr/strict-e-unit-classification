import TensorConstants

/-! The actual tensor flip restricts to an involutive algebra automorphism
of the diagonal constants. It is not yet declared a Hopf antipode. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- Swapping factors commutes with the actual diagonal derivation. -/
theorem relativeTensorDerivation_flip
    (dB : Derivation k B B) (dR : Derivation k R R)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (z : R ⊗[B] R) :
    relativeTensorDerivation dB dR hR (Algebra.TensorProduct.comm B R R z) =
      Algebra.TensorProduct.comm B R R (relativeTensorDerivation dB dR hR z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    simp only [Algebra.TensorProduct.comm_tmul, relativeTensorDerivation_tmul, map_add]
    exact add_comm _ _
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction of tensor swap to the genuine constant algebra. -/
def pvConstantFlip
    (dB : Derivation k B B) (dR : Derivation k R R)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) :
    pvConstantAlgebra dB dR hR ≃ₐ[k] pvConstantAlgebra dB dR hR where
  toFun z := ⟨Algebra.TensorProduct.comm B R R z, by
    change relativeTensorDerivation dB dR hR (Algebra.TensorProduct.comm B R R z) = 0
    rw [relativeTensorDerivation_flip, z.property, map_zero]⟩
  invFun z := ⟨Algebra.TensorProduct.comm B R R z, by
    change relativeTensorDerivation dB dR hR (Algebra.TensorProduct.comm B R R z) = 0
    rw [relativeTensorDerivation_flip, z.property, map_zero]⟩
  left_inv z := by
    apply Subtype.ext
    exact (Algebra.TensorProduct.comm B R R).symm_apply_apply (z : R ⊗[B] R)
  right_inv z := by
    apply Subtype.ext
    exact (Algebra.TensorProduct.comm B R R).apply_symm_apply (z : R ⊗[B] R)
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  commutes' c := by
    apply Subtype.ext
    exact ((Algebra.TensorProduct.comm B R R).restrictScalars k).commutes c

@[simp] theorem pvConstantFlip_coe
    (dB : Derivation k B B) (dR : Derivation k R R)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (z : pvConstantAlgebra dB dR hR) :
    (pvConstantFlip dB dR hR z : R ⊗[B] R) =
      Algebra.TensorProduct.comm B R R (z : R ⊗[B] R) := rfl

@[simp] theorem pvConstantFlip_involutive
    (dB : Derivation k B B) (dR : Derivation k R R)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (z : pvConstantAlgebra dB dR hR) :
    pvConstantFlip dB dR hR (pvConstantFlip dB dR hR z) = z := by
  apply Subtype.ext
  exact (Algebra.TensorProduct.comm B R R).symm_apply_apply (z : R ⊗[B] R)
end StrictEUnit

#print axioms StrictEUnit.relativeTensorDerivation_flip
#print axioms StrictEUnit.pvConstantFlip
#print axioms StrictEUnit.pvConstantFlip_coe
#print axioms StrictEUnit.pvConstantFlip_involutive
