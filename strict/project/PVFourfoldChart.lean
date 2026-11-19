import PVRightCounitLaw

/-! Actual recursive fourfold tensor chart, without a coassociativity premise. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra k H] [Algebra B R] [IsScalarTower k B R]

def pvFourfoldChart (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    R ⊗[k] (H ⊗[k] (H ⊗[k] H)) ≃ₐ[R] R ⊗[B] (R ⊗[B] (R ⊗[B] R)) :=
  (leftAlgebraAssoc (B:=k) (R:=R) H (H ⊗[k] H)).symm |>.trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl (R:=k) (A₁:=H ⊗[k] H))).trans
      ((mixedAlgebraAssoc (k:=k) (B:=B)).trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=R) (A₁:=R))
          ((pvTripleChart e).restrictScalars B))))

@[simp] theorem pvFourfoldChart_tmul
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (r : R) (h : H) (z : H ⊗[k] H) :
    pvFourfoldChart e (r ⊗ₜ[k] (h ⊗ₜ[k] z)) =
      Algebra.TensorProduct.map (AlgHom.id B R) ((pvTripleChart e).toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (e (r ⊗ₜ[k] h) ⊗ₜ[k] z)) := rfl

/-- Insert a unit between the final two factors of the triple tensor. -/
def pvInsertThird : R ⊗[B] (R ⊗[B] R) →ₐ[R] R ⊗[B] (R ⊗[B] (R ⊗[B] R)) :=
  Algebra.TensorProduct.map (AlgHom.id R R)
    (Algebra.TensorProduct.map (AlgHom.id B R)
      (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R))

@[simp] theorem pvInsertThird_tmul (r s t : R) :
    pvInsertThird (B:=B) (r ⊗ₜ[B] (s ⊗ₜ[B] t)) =
      r ⊗ₜ[B] (s ⊗ₜ[B] ((1:R) ⊗ₜ[B] t)) := rfl

/-- Insert a unit immediately after the first factor. -/
def pvInsertSecond : R ⊗[B] (R ⊗[B] R) →ₐ[R] R ⊗[B] (R ⊗[B] (R ⊗[B] R)) :=
  Algebra.TensorProduct.map (AlgHom.id R R)
    (Algebra.TensorProduct.includeRight : (R ⊗[B] R) →ₐ[B] R ⊗[B] (R ⊗[B] R))

@[simp] theorem pvInsertSecond_tmul (r : R) (z : R ⊗[B] R) :
    pvInsertSecond (B:=B) (r ⊗ₜ[B] z) = r ⊗ₜ[B] ((1:R) ⊗ₜ[B] z) := rfl

end StrictEUnit
#print axioms StrictEUnit.pvFourfoldChart
#print axioms StrictEUnit.pvFourfoldChart_tmul
#print axioms StrictEUnit.pvInsertThird
#print axioms StrictEUnit.pvInsertThird_tmul
#print axioms StrictEUnit.pvInsertSecond
#print axioms StrictEUnit.pvInsertSecond_tmul
