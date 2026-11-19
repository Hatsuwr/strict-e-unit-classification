import PVLeftCounitLaw
import TypedMorphismMaps

/-! The right counit law for the actual descended comultiplication. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

def pvTripleContractRight : R ⊗[B] (R ⊗[B] R) →ₐ[R] R ⊗[B] R :=
  Algebra.TensorProduct.map (AlgHom.id R R) (diagonalTensorMul (B:=B) (R:=R))

@[simp] theorem pvTripleContractRight_tmul (r : R) (z : R ⊗[B] R) :
    pvTripleContractRight (B:=B) (r ⊗ₜ[B] z) = r ⊗ₜ[B] diagonalTensorMul z := rfl

theorem pvTripleContractRight_insert (z : R ⊗[B] R) :
    pvTripleContractRight (pvMiddleInsertion (k:=k) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s => simp only [pvMiddleInsertion_tmul, pvTripleContractRight_tmul,
      diagonalTensorMul_tmul, one_mul]

def pvRightCounitContraction
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r) :
    (pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb) →ₐ[k]
      pvConstantAlgebra dB d hb :=
  Algebra.TensorProduct.lift (AlgHom.id k _)
    ((Algebra.ofId k _).comp (candidateCounit dB d hb hc))
    (fun _ _ => Commute.all _ _)

theorem pvTripleContractRight_leg
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (g : pvConstantAlgebra dB d hb) (z : R ⊗[B] R) :
    pvTripleContractRight
      (Algebra.TensorProduct.map (AlgHom.id B R)
        ((AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he).toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] g))) =
      z * ((1:R) ⊗ₜ[B] algebraMap k R (candidateCounit dB d hb hc g)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [zero_tmul, TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, zero_mul]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, add_tmul, hx, hy, add_mul]
  | tmul r s =>
    simp only [mixedAlgebraAssoc_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply, pvTripleContractRight_tmul]
    change r ⊗ₜ[B] diagonalTensorMul (pvConstantMultiplication dB d hb (s ⊗ₜ[k] g)) = _
    rw [pvConstantMultiplication_tmul, map_mul, diagonalTensorMul_tmul,
      mul_one, ← candidateCounit_scalar dB d hb hc g,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pvTripleContractRight_chart
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (z : pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb) :
    pvTripleContractRight
      (pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)
        ((1:R) ⊗ₜ[k] z)) =
      (pvRightCounitContraction dB d hb hc z : R ⊗[B] R) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [tmul_zero, pvTripleChart_zero]
    simp only [map_zero, ZeroMemClass.coe_zero]
  | add x y hx hy =>
    rw [tmul_add, pvTripleChart_add]
    simp only [map_add, hx, hy]
    rfl
  | tmul h g =>
    rw [pvTripleChart_tmul, pvTripleContractRight_leg dB d hb hc he]
    change pvConstantMultiplication dB d hb ((1:R) ⊗ₜ[k] h) *
      ((1:R) ⊗ₜ[B] algebraMap k R (candidateCounit dB d hb hc g)) = _
    simp only [pvConstantMultiplication_tmul,
      show (1:R) ⊗ₜ[B] (1:R) = 1 from rfl, one_mul]
    have hs (c:k) : (1:R) ⊗ₜ[B] algebraMap k R c = algebraMap k R c ⊗ₜ[B] (1:R) := by
      simpa only [IsScalarTower.algebraMap_apply k B R] using
        (Algebra.TensorProduct.tmul_one_eq_one_tmul (A:=R) (B:=R) (algebraMap k B c)).symm
    rw [hs]
    rfl

theorem pvConstantComultiplication_right_counit
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (h : pvConstantAlgebra dB d hb) :
    pvRightCounitContraction dB d hb hc
      (pvConstantComultiplication dB d hb he hc h) = h := by
  apply Subtype.ext
  rw [← pvTripleContractRight_chart dB d hb hc he,
    pvConstantComultiplication_spec, pvTripleContractRight_insert]

end StrictEUnit
#print axioms StrictEUnit.pvTripleContractRight
#print axioms StrictEUnit.pvTripleContractRight_tmul
#print axioms StrictEUnit.pvTripleContractRight_insert
#print axioms StrictEUnit.pvRightCounitContraction
#print axioms StrictEUnit.pvTripleContractRight_leg

#print axioms StrictEUnit.pvTripleContractRight_chart
#print axioms StrictEUnit.pvConstantComultiplication_right_counit
