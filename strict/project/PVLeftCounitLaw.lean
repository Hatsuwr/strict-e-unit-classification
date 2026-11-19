import PVConstantComultiplication
import CandidateCounit

/-! The left counit law for the descended comultiplication. -/
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

/-- Typed chart identities avoid ambiguous morphism-class inference after specialization. -/
@[simp] theorem pvTripleChart_zero {H : Type*} [CommRing H] [Algebra k H]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    pvTripleChart e (0 : R ⊗[k] (H ⊗[k] H)) = (0 : R ⊗[B] (R ⊗[B] R)) :=
  (pvTripleChart e).map_zero

@[simp] theorem pvTripleChart_add {H : Type*} [CommRing H] [Algebra k H]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (x y : R ⊗[k] (H ⊗[k] H)) :
    pvTripleChart e (x + y) = pvTripleChart e x + pvTripleChart e y :=
  (pvTripleChart e).map_add x y

/-- Multiply the first two of three relative factors. -/
def pvTripleContractLeft : R ⊗[B] (R ⊗[B] R) →ₐ[R] R ⊗[B] R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (R ⊗[B] R))
    (AlgHom.id B (R ⊗[B] R)) (fun _ _ => Commute.all _ _)

@[simp] theorem pvTripleContractLeft_tmul (r : R) (z : R ⊗[B] R) :
    pvTripleContractLeft (B:=B) (r ⊗ₜ[B] z) = (r ⊗ₜ[B] (1:R)) * z := rfl

theorem pvTripleContractLeft_insert (z : R ⊗[B] R) :
    pvTripleContractLeft (pvMiddleInsertion (k:=k) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s => simp only [pvMiddleInsertion_tmul, pvTripleContractLeft_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem pvTripleContractLeft_leg {H : Type*} [CommRing H] [Algebra k H]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (g : H) (z : R ⊗[B] R) :
    pvTripleContractLeft
      (Algebra.TensorProduct.map (AlgHom.id B R) (e.toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] g))) =
      e (diagonalTensorMul z ⊗ₜ[k] g) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | tmul r s =>
    simp only [mixedAlgebraAssoc_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply, pvTripleContractLeft_tmul,
      diagonalTensorMul_tmul]
    change (r ⊗ₜ[B] (1:R)) * e (s ⊗ₜ[k] g) = e ((r*s) ⊗ₜ[k] g)
    have hr : e (r ⊗ₜ[k] (1:H)) = r ⊗ₜ[B] (1:R) := e.commutes r
    rw [← hr, ← map_mul]
    congr 1
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Contraction of the first H factor by the constructed counit. -/
def pvLeftCounitContraction
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r) :
    (pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb) →ₐ[k]
      pvConstantAlgebra dB d hb :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId k _).comp (candidateCounit dB d hb hc)) (AlgHom.id k _)
    (fun _ _ => Commute.all _ _)

theorem pvTripleContractLeft_chart
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (z : pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb) :
    pvTripleContractLeft
      (pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)
        ((1:R) ⊗ₜ[k] z)) =
      (pvLeftCounitContraction dB d hb hc z : R ⊗[B] R) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [tmul_zero, pvTripleChart_zero]
    simp only [map_zero, ZeroMemClass.coe_zero]
  | add x y hx hy =>
    rw [tmul_add, pvTripleChart_add]
    simp only [map_add, hx, hy]
    rfl
  | tmul h g =>
    rw [pvTripleChart_tmul, pvTripleContractLeft_leg]
    change pvConstantMultiplication dB d hb
      (diagonalTensorMul (pvConstantMultiplication dB d hb ((1:R) ⊗ₜ[k] h)) ⊗ₜ[k] g) = _
    simp only [pvConstantMultiplication_tmul,
      show (1:R) ⊗ₜ[B] (1:R) = 1 from rfl, one_mul]
    rw [← candidateCounit_scalar dB d hb hc h]
    rfl

/-- The actual left counit law follows from the triple descent identity. -/
theorem pvConstantComultiplication_left_counit
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (h : pvConstantAlgebra dB d hb) :
    pvLeftCounitContraction dB d hb hc
      (pvConstantComultiplication dB d hb he hc h) = h := by
  apply Subtype.ext
  rw [← pvTripleContractLeft_chart dB d hb hc he,
    pvConstantComultiplication_spec, pvTripleContractLeft_insert]

end StrictEUnit
#print axioms StrictEUnit.pvTripleContractLeft
#print axioms StrictEUnit.pvTripleContractLeft_tmul
#print axioms StrictEUnit.pvTripleContractLeft_insert
#print axioms StrictEUnit.pvTripleContractLeft_leg
#print axioms StrictEUnit.pvLeftCounitContraction

#print axioms StrictEUnit.pvTripleContractLeft_chart
#print axioms StrictEUnit.pvConstantComultiplication_left_counit
