import WeightBaseChange

/-! The target chart built from a torsor chart by tensor reassociation.
No coalgebra or bialgebra structure on the cover ring is assumed. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {B R H : Type*} [CommRing B] [CommRing R] [CommRing H]
  [Algebra B R] [Algebra B H]

/-- The usual associator, retaining the left-factor algebra structure. -/
def leftAlgebraAssoc (S T : Type*) [CommRing S] [CommRing T]
    [Algebra B S] [Algebra B T] :
    (R ⊗[B] S) ⊗[B] T ≃ₐ[R] R ⊗[B] (S ⊗[B] T) :=
  { (Algebra.TensorProduct.assoc B R S T).toRingEquiv with
    commutes' := fun r => by
      change (Algebra.TensorProduct.assoc B R S T)
        ((r ⊗ₜ[B] (1:S)) ⊗ₜ[B] (1:T)) = r ⊗ₜ[B] (1:S ⊗[B] T)
      rfl }

/-- Tensor the actual chart with the identity of H, with the required reassociations. -/
def torsorTargetChart (e : R ⊗[B] R ≃ₐ[R] R ⊗[B] H) :
    R ⊗[B] (R ⊗[B] H) ≃ₐ[R] R ⊗[B] (H ⊗[B] H) :=
  (leftAlgebraAssoc (B:=B) (R:=R) R H).symm |>.trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl (R:=B) (A₁:=H))).trans
      (leftAlgebraAssoc (B:=B) (R:=R) H H))

@[simp] theorem torsorTargetChart_tmul
    (e : R ⊗[B] R ≃ₐ[R] R ⊗[B] H) (r s : R) (h : H) :
    torsorTargetChart e (r ⊗ₜ[B] (s ⊗ₜ[B] h)) =
      Algebra.TensorProduct.assoc B R H H (e (r ⊗ₜ[B] s) ⊗ₜ[B] h) := rfl

/-- Reassociation of a right unit is the scalar-extended inclusion. -/
theorem assoc_tmul_one (z : R ⊗[B] H) :
    Algebra.TensorProduct.assoc B R H H (z ⊗ₜ[B] (1:H)) =
      weightBaseChangeAlgHom R
        (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r h => rfl
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- The inclusion square commutes for every left-algebra chart. -/
theorem torsorTargetChart_includeLeft
    (e : R ⊗[B] R ≃ₐ[R] R ⊗[B] H) (x : R ⊗[B] R) :
    torsorTargetChart e
      (weightBaseChangeAlgHom R
        (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] H) x) =
      weightBaseChangeAlgHom R
        (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) (e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s => exact assoc_tmul_one (e (r ⊗ₜ[B] s))
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The character multiplier is unchanged in the final factor. -/
theorem torsorTargetChart_multiplier
    (e : R ⊗[B] R ≃ₐ[R] R ⊗[B] H) (h : H) :
    torsorTargetChart e ((1:R) ⊗ₜ[B] ((1:R) ⊗ₜ[B] h)) =
      (1:R) ⊗ₜ[B] ((1:H) ⊗ₜ[B] h) := by
  rw [torsorTargetChart_tmul]
  change Algebra.TensorProduct.assoc B R H H (e 1 ⊗ₜ[B] h) = _
  rw [map_one]
  rfl

#print axioms leftAlgebraAssoc
#print axioms torsorTargetChart
#print axioms torsorTargetChart_tmul
#print axioms assoc_tmul_one
#print axioms torsorTargetChart_includeLeft
#print axioms torsorTargetChart_multiplier
end StrictEUnit
