import TypedMorphismMaps
import PVConstantBialgebra
import PVConstantFlip

/-! The actual tensor flip satisfies both antipode identities. -/
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
variable (dB : Derivation k B B) (d : Derivation k R R)
  (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
local notation "H" => pvConstantAlgebra dB d hb
local notation "e" => AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he
local notation "Δ" => pvConstantComultiplication dB d hb he hc
local notation "ε" => candidateCounit dB d hb hc
local notation "S" => pvConstantFlip dB d hb

/-- Fold the triple tensor by identifying its first and last factors. -/
def pvAntipodeFold : R ⊗[B] (R ⊗[B] R) →ₐ[B] R ⊗[B] R :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R)
    (AlgHom.id B (R ⊗[B] R)) (fun _ _ => Commute.all _ _)

@[simp] theorem pvAntipodeFold_tmul (r:R) (z:R ⊗[B] R) :
    pvAntipodeFold (B:=B) (r ⊗ₜ[B] z) = ((1:R) ⊗ₜ[B] r) * z := rfl

theorem pvAntipodeFold_append (z:R ⊗[B] R) :
    pvAntipodeFold (pvAppendOnePair z) = Algebra.TensorProduct.comm B R R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r s =>
    change ((1:R) ⊗ₜ[B] r) * (s ⊗ₜ[B] (1:R)) = s ⊗ₜ[B] r
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem pvAntipodeFold_insert (z:R ⊗[B] R) :
    pvAntipodeFold (pvMiddleInsertion (k:=k) z) =
      (1:R) ⊗ₜ[B] diagonalTensorMul z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, tmul_add, hx, hy]
  | tmul r s =>
    simp only [pvMiddleInsertion_tmul, pvAntipodeFold_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, diagonalTensorMul_tmul]

def pvAntipodeContractionLeft : H ⊗[k] H →ₐ[k] H :=
  Algebra.TensorProduct.lift (S).toAlgHom (AlgHom.id k H) (fun _ _ => Commute.all _ _)

def pvAntipodeContractionRight : H ⊗[k] H →ₐ[k] H :=
  Algebra.TensorProduct.lift (AlgHom.id k H) (S).toAlgHom (fun _ _ => Commute.all _ _)

theorem pvAntipodeFold_chart (z:H ⊗[k] H) :
    pvAntipodeFold (pvTripleChart e ((1:R) ⊗ₜ[k] z)) =
      (pvAntipodeContractionLeft dB d hb z : R ⊗[B] R) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, tmul_add, hx, hy]; rfl
  | tmul h g =>
    rw [pvTriple_pair_formula, TypedMaps.algHom_mul, pvAntipodeFold_append, pvAntipodeFold_tmul]
    simp only [pvConstantMultiplication_tmul,
      show (1:R) ⊗ₜ[B] (1:R) = 1 from rfl, one_mul]
    rfl

theorem pvAntipode_left (h:H) :
    pvAntipodeContractionLeft dB d hb (Δ h) = algebraMap k H (ε h) := by
  apply Subtype.ext
  rw [← pvAntipodeFold_chart dB d hb he, pvConstantComultiplication_spec,
    pvAntipodeFold_insert, ← candidateCounit_scalar dB d hb hc h]
  change (1:R) ⊗ₜ[B] algebraMap k R (ε h) = algebraMap k R (ε h) ⊗ₜ[B] (1:R)
  simpa only [IsScalarTower.algebraMap_apply k B R] using
    (Algebra.TensorProduct.tmul_one_eq_one_tmul (A:=R) (B:=R) (algebraMap k B (ε h))).symm

theorem pvAntipode_contractions_flip (z:H ⊗[k] H) :
    S (pvAntipodeContractionLeft dB d hb z) = pvAntipodeContractionRight dB d hb z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul h g =>
    change S (S h * g) = h * S g
    rw [TypedMaps.algEquiv_mul, pvConstantFlip_involutive]

theorem pvAntipode_right (h:H) :
    pvAntipodeContractionRight dB d hb (Δ h) = algebraMap k H (ε h) := by
  rw [← pvAntipode_contractions_flip, pvAntipode_left]
  exact (S).commutes (ε h)

end StrictEUnit
#print axioms StrictEUnit.pvAntipodeFold
#print axioms StrictEUnit.pvAntipodeFold_tmul
#print axioms StrictEUnit.pvAntipodeFold_append
#print axioms StrictEUnit.pvAntipodeFold_insert
#print axioms StrictEUnit.pvAntipodeContractionLeft
#print axioms StrictEUnit.pvAntipodeContractionRight
#print axioms StrictEUnit.pvAntipodeFold_chart
#print axioms StrictEUnit.pvAntipode_left
#print axioms StrictEUnit.pvAntipode_contractions_flip
#print axioms StrictEUnit.pvAntipode_right
