import PVFourfoldLinear
import TypedMorphismMaps

/-! Coassociativity via the actual fourfold chart. -/
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

local instance pvCoassocConstantCommRing : CommRing H :=
  (pvConstantAlgebra dB d hb).toCommRing
local instance pvCoassocConstantSemiring : Semiring H :=
  (pvConstantAlgebra dB d hb).toSemiring
local instance pvCoassocConstantAddCommGroup : AddCommGroup H :=
  @Ring.toAddCommGroup _ (pvConstantAlgebra dB d hb).toRing
local instance pvCoassocConstantAddGroup : AddGroup H :=
  @AddCommGroup.toAddGroup _ (@Ring.toAddCommGroup _ (pvConstantAlgebra dB d hb).toRing)

theorem pvTripleChart_comul_scalar (r:R) (h:H) :
    pvTripleChart e (r ⊗ₜ[k] Δ h) =
      pvMiddleInsertion (k:=k) (pvConstantMultiplication dB d hb (r ⊗ₜ[k] h)) := by
  have hr : pvTripleChart e (r ⊗ₜ[k] (1:H ⊗[k] H)) =
      r ⊗ₜ[B] (1:R ⊗[B] R) := (pvTripleChart e).commutes r
  have ht : r ⊗ₜ[k] Δ h =
      (r ⊗ₜ[k] (1:H ⊗[k] H)) * ((1:R) ⊗ₜ[k] Δ h) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, TypedMaps.algEquiv_mul, hr, pvConstantComultiplication_spec,
    pvConstantMultiplication_tmul, TypedMaps.algHom_mul, pvMiddleInsertion_tmul]
  rfl

theorem pvFourfold_right_leg (g:H) (z:R ⊗[B] R) :
    Algebra.TensorProduct.map (AlgHom.id B R) ((pvTripleChart e).toAlgHom.restrictScalars B)
      (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] Δ g)) =
    pvInsertThird
      (Algebra.TensorProduct.map (AlgHom.id B R) ((e).toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] g))) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, zero_tmul, tmul_zero, zero_mul]
  | add x y hx hy =>
    simp only [add_tmul, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r s =>
    simp only [mixedAlgebraAssoc_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.restrictScalars_apply]
    change r ⊗ₜ[B] pvTripleChart e (s ⊗ₜ[k] Δ g) =
      r ⊗ₜ[B] pvMiddleInsertion (k:=k) (pvConstantMultiplication dB d hb (s ⊗ₜ[k] g))
    rw [pvTripleChart_comul_scalar]

theorem pvFourfold_right_diagram (z:H ⊗[k] H) :
    pvFourfoldChart e ((1:R) ⊗ₜ[k]
      Algebra.TensorProduct.map (AlgHom.id k H) Δ z) =
    pvInsertThird (pvTripleChart e ((1:R) ⊗ₜ[k] z)) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, zero_mul]
  | add x y hx hy =>
    simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, tmul_add, hx, hy]
  | tmul h g =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      pvFourfoldChart_tmul, pvTripleChart_tmul]
    exact pvFourfold_right_leg dB d hb he hc g (e ((1:R) ⊗ₜ[k] h))

/-- Append a unit to the relative tensor square. -/
def pvAppendOnePair : R ⊗[B] R →ₐ[R] R ⊗[B] (R ⊗[B] R) :=
  Algebra.TensorProduct.map (AlgHom.id R R)
    (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R)

def pvAppendOneTriple : R ⊗[B] (R ⊗[B] R) →ₐ[R] R ⊗[B] (R ⊗[B] (R ⊗[B] R)) :=
  Algebra.TensorProduct.map (AlgHom.id R R)
    ((pvAppendOnePair (B:=B) (R:=R)).restrictScalars B)

theorem pvTriple_pair_leg (z:R ⊗[B] R) (g:H) :
    Algebra.TensorProduct.map (AlgHom.id B R) ((e).toAlgHom.restrictScalars B)
      (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] g)) =
    pvAppendOnePair z * ((1:R) ⊗ₜ[B] (g:R ⊗[B] R)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, zero_tmul, tmul_zero, zero_mul]
  | add x y hx hy =>
    simp only [add_tmul, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy, add_mul]
  | tmul r s =>
    change r ⊗ₜ[B] pvConstantMultiplication dB d hb (s ⊗ₜ[k] g) =
      (r ⊗ₜ[B] (s ⊗ₜ[B] (1:R))) * ((1:R) ⊗ₜ[B] (g:R ⊗[B] R))
    rw [pvConstantMultiplication_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pvTriple_pair_formula (r:R) (h g:H) :
    pvTripleChart e (r ⊗ₜ[k] (h ⊗ₜ[k] g)) =
      pvAppendOnePair (pvConstantMultiplication dB d hb (r ⊗ₜ[k] h)) *
        ((1:R) ⊗ₜ[B] (g:R ⊗[B] R)) := by
  rw [pvTripleChart_tmul]
  exact pvTriple_pair_leg dB d hb he (pvConstantMultiplication dB d hb (r ⊗ₜ[k] h)) g

theorem pvFourfold_last_leg (z:R ⊗[B] R) (h g:H) :
    Algebra.TensorProduct.map (AlgHom.id B R) ((pvTripleChart e).toAlgHom.restrictScalars B)
      (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] (h ⊗ₜ[k] g))) =
    pvAppendOneTriple
      (Algebra.TensorProduct.map (AlgHom.id B R) ((e).toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (z ⊗ₜ[k] h))) *
      ((1:R) ⊗ₜ[B] ((1:R) ⊗ₜ[B] (g:R ⊗[B] R))) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, zero_tmul, tmul_zero, zero_mul]
  | add x y hx hy =>
    simp only [add_tmul, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy, add_mul]
  | tmul r s =>
    change r ⊗ₜ[B] pvTripleChart e (s ⊗ₜ[k] (h ⊗ₜ[k] g)) =
      (r ⊗ₜ[B] pvAppendOnePair (pvConstantMultiplication dB d hb (s ⊗ₜ[k] h))) *
        ((1:R) ⊗ₜ[B] ((1:R) ⊗ₜ[B] (g:R ⊗[B] R)))
    rw [pvTriple_pair_formula, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pvFourfold_last_formula (z:H ⊗[k] H) (g:H) :
    pvFourfoldChart e ((1:R) ⊗ₜ[k]
      (Algebra.TensorProduct.assoc k H H H (z ⊗ₜ[k] g))) =
    pvAppendOneTriple (pvTripleChart e ((1:R) ⊗ₜ[k] z)) *
      ((1:R) ⊗ₜ[B] ((1:R) ⊗ₜ[B] (g:R ⊗[B] R))) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, zero_mul]
  | add x y hx hy =>
    simp only [add_tmul, TypedMaps.algEquiv_add, TypedMaps.algHom_add, tmul_add, hx, hy, add_mul]
  | tmul h j =>
    change pvFourfoldChart e ((1:R) ⊗ₜ[k] (h ⊗ₜ[k] (j ⊗ₜ[k] g))) = _
    rw [pvFourfoldChart_tmul, pvTripleChart_tmul]
    exact pvFourfold_last_leg dB d hb he (e ((1:R) ⊗ₜ[k] h)) j g

theorem pvAppend_insert (z:R ⊗[B] R) :
    pvAppendOneTriple (pvMiddleInsertion (k:=k) z) =
      pvInsertSecond (pvAppendOnePair z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, zero_tmul, tmul_zero, zero_mul]
  | add x y hx hy =>
    simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r s => rfl

theorem pvFourfold_left_diagram (z:H ⊗[k] H) :
    pvFourfoldChart e ((1:R) ⊗ₜ[k]
      (Algebra.TensorProduct.assoc k H H H
        (Algebra.TensorProduct.map Δ (AlgHom.id k H) z))) =
    pvInsertSecond (pvTripleChart e ((1:R) ⊗ₜ[k] z)) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, zero_mul]
  | add x y hx hy =>
    simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, tmul_add, hx, hy]
  | tmul h g =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [pvFourfold_last_formula, pvConstantComultiplication_spec,
      pvAppend_insert, pvTriple_pair_formula, TypedMaps.algHom_mul]
    simp only [pvConstantMultiplication_tmul,
      show (1:R) ⊗ₜ[B] (1:R) = 1 from rfl, one_mul]
    rfl

theorem pvDoubleInsertion_eq (z:R ⊗[B] R) :
    pvInsertSecond (pvMiddleInsertion (k:=k) z) =
      pvInsertThird (pvMiddleInsertion (k:=k) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, zero_tmul, tmul_zero, zero_mul]
  | add x y hx hy =>
    simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r s => rfl

/-- Coassociativity of the constructed comultiplication, proved by the
injective fourfold chart and two genuine insertion diagrams. -/
theorem pvConstantComultiplication_coassoc (h:H) :
    Algebra.TensorProduct.assoc k H H H
      (Algebra.TensorProduct.map Δ (AlgHom.id k H) (Δ h)) =
    Algebra.TensorProduct.map (AlgHom.id k H) Δ (Δ h) := by
  letI : Module.Free k (H ⊗[k] (H ⊗[k] H)) :=
    Module.Free.of_divisionRing k (H ⊗[k] (H ⊗[k] H))
  letI : Module.Flat k (H ⊗[k] (H ⊗[k] H)) := Module.Flat.of_free
  apply Algebra.TensorProduct.includeRight_injective (R:=k) (A:=R)
    (RingHom.injective (algebraMap k R))
  change (1:R) ⊗ₜ[k] _ = (1:R) ⊗ₜ[k] _
  apply pvFourfoldChart_injective e
  rw [pvFourfold_left_diagram, pvFourfold_right_diagram,
    pvConstantComultiplication_spec]
  exact pvDoubleInsertion_eq (h:R ⊗[B] R)

end StrictEUnit
#print axioms StrictEUnit.pvTripleChart_comul_scalar
#print axioms StrictEUnit.pvFourfold_right_leg
#print axioms StrictEUnit.pvFourfold_right_diagram

#print axioms StrictEUnit.pvAppendOnePair
#print axioms StrictEUnit.pvAppendOneTriple
#print axioms StrictEUnit.pvTriple_pair_leg
#print axioms StrictEUnit.pvTriple_pair_formula
#print axioms StrictEUnit.pvFourfold_last_leg
#print axioms StrictEUnit.pvFourfold_last_formula
#print axioms StrictEUnit.pvAppend_insert
#print axioms StrictEUnit.pvFourfold_left_diagram

#print axioms StrictEUnit.pvDoubleInsertion_eq
#print axioms StrictEUnit.pvConstantComultiplication_coassoc
