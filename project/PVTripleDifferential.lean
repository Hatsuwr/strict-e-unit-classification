import PVTripleChart
import CandidateDifferentialCoaction

/-! Genuine diagonal differentiation of the triple chart. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra k H] [Algebra B R] [IsScalarTower k B R]

theorem relativeTensorDerivation_base
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) (b : B) :
    relativeTensorDerivation dB d hb (algebraMap B (R ⊗[B] R) b) =
      algebraMap B (R ⊗[B] R) (dB b) := by
  change relativeTensorDerivation dB d hb ((algebraMap B R b) ⊗ₜ[B] (1:R)) = _
  simp only [relativeTensorDerivation_tmul, hb, Derivation.map_one_eq_zero,
    tmul_zero, add_zero]
  rfl

/-- The actual sum of differentiation in all three relative factors. -/
def pvTripleDerivation
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) :
    Derivation k (R ⊗[B] (R ⊗[B] R)) (R ⊗[B] (R ⊗[B] R)) :=
  mixedRelativeTensorDerivation dB d (relativeTensorDerivation dB d hb) hb
    (relativeTensorDerivation_base dB d hb)

@[simp] theorem pvTripleDerivation_tmul
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (r : R) (z : R ⊗[B] R) :
    pvTripleDerivation dB d hb (r ⊗ₜ[B] z) =
      d r ⊗ₜ[B] z + r ⊗ₜ[B] relativeTensorDerivation dB d hb z := rfl

theorem pvTripleChart_leg_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (he : ∀ z, relativeTensorDerivation dB d hb (e z) = e (tensorDerivation d z))
    (g : H) (z : R ⊗[B] R) :
    pvTripleDerivation dB d hb
      (Algebra.TensorProduct.map (AlgHom.id B R) (e.toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] g))) =
    Algebra.TensorProduct.map (AlgHom.id B R) (e.toAlgHom.restrictScalars B)
      (mixedAlgebraAssoc (k:=k) (B:=B)
        (relativeTensorDerivation dB d hb z ⊗ₜ[k] g)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | tmul r s =>
    simp only [mixedAlgebraAssoc_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.coe_algHom, pvTripleDerivation_tmul, he, tensorDerivation_tmul,
      relativeTensorDerivation_tmul, add_tmul, map_add]
    change d r ⊗ₜ[B] e (s ⊗ₜ[k] g) + r ⊗ₜ[B] relativeTensorDerivation dB d hb (e (s ⊗ₜ[k] g)) = _
    rw [he, tensorDerivation_tmul]
    rfl

theorem pvTripleChart_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (he : ∀ z, relativeTensorDerivation dB d hb (e z) = e (tensorDerivation d z))
    (z : R ⊗[k] (H ⊗[k] H)) :
    pvTripleDerivation dB d hb (pvTripleChart e z) =
      pvTripleChart e (tensorDerivation d z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul h g =>
      rw [pvTripleChart_tmul, pvTripleChart_leg_differential dB d hb e he,
        he, tensorDerivation_tmul, tensorDerivation_tmul, pvTripleChart_tmul]

end StrictEUnit
#print axioms StrictEUnit.relativeTensorDerivation_base
#print axioms StrictEUnit.pvTripleDerivation
#print axioms StrictEUnit.pvTripleDerivation_tmul
#print axioms StrictEUnit.pvTripleChart_leg_differential
#print axioms StrictEUnit.pvTripleChart_differential
