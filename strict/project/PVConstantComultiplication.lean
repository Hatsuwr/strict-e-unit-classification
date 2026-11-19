import PVTripleDifferential

/-! Comultiplication descends from insertion in the actual triple tensor.
This file constructs an algebra homomorphism, not its coalgebra laws. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- Insert the middle unit, retaining the first and third tensor factors. -/
def pvMiddleInsertion : R ⊗[B] R →ₐ[k] R ⊗[B] (R ⊗[B] R) :=
  (Algebra.TensorProduct.map (AlgHom.id B R)
    (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R)).restrictScalars k

@[simp] theorem pvMiddleInsertion_tmul (r s : R) :
    pvMiddleInsertion (k:=k) (B:=B) (r ⊗ₜ[B] s) = r ⊗ₜ[B] ((1:R) ⊗ₜ[B] s) := rfl

theorem pvMiddleInsertion_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) (z : R ⊗[B] R) :
    pvTripleDerivation dB d hb (pvMiddleInsertion (k:=k) z) =
      pvMiddleInsertion (k:=k) (relativeTensorDerivation dB d hb z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s =>
    simp only [pvMiddleInsertion_tmul, pvTripleDerivation_tmul,
      relativeTensorDerivation_tmul, Derivation.map_one_eq_zero,
      zero_tmul, zero_add, map_add]

/-- Pulling an inserted constant through the actual triple chart preserves constants. -/
theorem pvMiddleInsertion_preimage_constant
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (h : pvConstantAlgebra dB d hb) :
    tensorDerivation d
      ((pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)).symm
        (pvMiddleInsertion (k:=k) (h : R ⊗[B] R))) = 0 := by
  let e := pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)
  have hz : e (0 : R ⊗[k] (pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb)) =
      (0 : R ⊗[B] (R ⊗[B] R)) := e.map_zero
  apply e.injective
  rw [← pvTripleChart_differential dB d hb _
    (pvConstantMultiplication_differential dB d hb), AlgEquiv.apply_symm_apply,
    pvMiddleInsertion_differential]
  change pvMiddleInsertion (k:=k) (relativeTensorDerivation dB d hb (h:R ⊗[B] R)) = e 0
  rw [h.property, hz]
  exact (pvMiddleInsertion (k:=k) (B:=B) (R:=R)).map_zero

/-- The inserted constant, pulled through the genuine triple chart, is a constant. -/
def pvComultiplicationConstantLift
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb)) :
    pvConstantAlgebra dB d hb →ₐ[k]
      derivationConstants (tensorDerivation
        (H:=pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb) d) :=
  ((((pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)).symm.toAlgHom.restrictScalars k).comp
    (pvMiddleInsertion (k:=k))).comp (pvConstantAlgebra dB d hb).val).codRestrict _
      (fun h => pvMiddleInsertion_preimage_constant dB d hb he h)

/-- Actual descended comultiplication. Bijectivity of constant multiplication
and exact constants of R are explicit inputs; no comultiplication is assumed. -/
def pvConstantComultiplication [Nontrivial R]
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (hc : ∀ r : R, d r = 0 → ∃ c : k, algebraMap k R c = r) :
    pvConstantAlgebra dB d hb →ₐ[k]
      pvConstantAlgebra dB d hb ⊗[k] pvConstantAlgebra dB d hb :=
  (tensorConstantsEquiv d hc).symm.toAlgHom.comp
    (pvComultiplicationConstantLift dB d hb he)

/-- The defining descent identity holds in the genuine triple tensor ring. -/
theorem pvConstantComultiplication_spec [Nontrivial R]
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb))
    (hc : ∀ r : R, d r = 0 → ∃ c : k, algebraMap k R c = r)
    (h : pvConstantAlgebra dB d hb) :
    pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)
      ((1:R) ⊗ₜ[k] pvConstantComultiplication dB d hb he hc h) =
      pvMiddleInsertion (k:=k) (h:R ⊗[B] R) := by
  have hh := congrArg Subtype.val ((tensorConstantsEquiv d hc).apply_symm_apply
    (pvComultiplicationConstantLift dB d hb he h))
  change (1:R) ⊗ₜ[k] pvConstantComultiplication dB d hb he hc h =
    (pvTripleChart (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)).symm
      (pvMiddleInsertion (k:=k) (h:R ⊗[B] R)) at hh
  rw [hh, AlgEquiv.apply_symm_apply]

end StrictEUnit
#print axioms StrictEUnit.pvMiddleInsertion
#print axioms StrictEUnit.pvMiddleInsertion_tmul
#print axioms StrictEUnit.pvMiddleInsertion_differential
#print axioms StrictEUnit.pvComultiplicationConstantLift
#print axioms StrictEUnit.pvConstantComultiplication

#print axioms StrictEUnit.pvConstantComultiplication_spec
