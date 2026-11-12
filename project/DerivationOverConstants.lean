import BaseFractionConstants

/-! A derivation annihilating the actual scalar algebra map is bundled over
those scalars. This closes a representation issue, not a new constants theorem. -/
noncomputable section
set_option maxHeartbeats 200000
namespace StrictEUnit

/-- Upgrade an actual integer-linear derivation to a k-derivation using its
proved vanishing on k. The k-scalar law follows from Leibniz. -/
def derivationOverConstants {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra ℤ A]
    (D : Derivation ℤ A A) (h : ∀ c : k, D (algebraMap k A c) = 0) :
    Derivation k A A where
  toFun := D
  map_add' := D.map_add
  map_smul' c x := by
    rw [Algebra.smul_def, D.leibniz, h c, smul_zero, add_zero]
    simp only [smul_eq_mul, RingHom.id_apply, Algebra.smul_def]
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

@[simp] theorem derivationOverConstants_apply {k A : Type*}
    [CommRing k] [CommRing A] [Algebra k A] [Algebra ℤ A]
    (D : Derivation ℤ A A) (h : ∀ c : k, D (algebraMap k A c) = 0) (a : A) :
    derivationOverConstants D h a = D a := rfl

/-- The constructed base fraction derivation, now bundled over its actual
constant field k without any additional mathematical premise. -/
def baseFractionKDerivation {k : Type*} [Field k] [CharZero k]
    (N : ℕ) (hN : N ≠ 0) :
    Derivation k (FractionRing (LaurentLogBase k)) (FractionRing (LaurentLogBase k)) :=
  derivationOverConstants (k := k) (A := FractionRing (LaurentLogBase k))
    (baseFractionDerivation (k := k) N hN) (fun c =>
    (baseFractionDerivation_constants_algebraMap (k := k) N hN _).mpr ⟨c, rfl⟩)

@[simp] theorem baseFractionKDerivation_apply {k : Type*} [Field k] [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (x : FractionRing (LaurentLogBase k)) :
    baseFractionKDerivation (k := k) N hN x = baseFractionDerivation (k := k) N hN x := rfl
end StrictEUnit
#print axioms StrictEUnit.derivationOverConstants
#print axioms StrictEUnit.derivationOverConstants_apply
#print axioms StrictEUnit.baseFractionKDerivation
#print axioms StrictEUnit.baseFractionKDerivation_apply
