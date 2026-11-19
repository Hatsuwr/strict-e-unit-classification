import RationalDerivationExtension

/-! Pulling a derivation back through an injective ring map. Image closure
is proved for fraction fields from compatibility on the original ring. -/
noncomputable section
namespace StrictEUnit
section Pullback
variable {F L : Type*} [Field F] [Field L] [Algebra ℤ F] [Algebra ℤ L]
variable (i : F →+* L) (hi : Function.Injective i) (d : Derivation ℤ L L)
variable (hclosed : ∀ x : F, ∃ y : F, i y = d (i x))

def derivationPreimage (x : F) : F := Classical.choose (hclosed x)

omit [Algebra ℤ F] in
theorem derivationPreimage_spec (x : F) :
    i (derivationPreimage i d hclosed x) = d (i x) := Classical.choose_spec (hclosed x)

def derivationPreimageAddHom : F →+ F where
  toFun := derivationPreimage i d hclosed
  map_zero' := by
    apply hi
    simp only [derivationPreimage_spec, map_zero]
  map_add' := by
    intro x y
    apply hi
    simp only [derivationPreimage_spec, map_add]

def injectiveDerivationPullback : Derivation ℤ F F where
  toFun := derivationPreimage i d hclosed
  map_add' := (derivationPreimageAddHom i hi d hclosed).map_add
  map_smul' := by
    intro c x
    have h := (derivationPreimageAddHom i hi d hclosed).map_zsmul x c
    rw [Algebra.smul_def]
    have hm : algebraMap ℤ F c = (c:F) := map_intCast _ c
    rw [hm]
    simpa only [RingHom.id_apply, zsmul_eq_mul] using h
  map_one_eq_zero' := by
    apply hi
    change i (derivationPreimage i d hclosed 1) = i 0
    simp only [derivationPreimage_spec, map_one, d.map_one_eq_zero, map_zero]
  leibniz' := by
    intro x y
    apply hi
    change i (derivationPreimage i d hclosed (x*y)) =
      i (x * derivationPreimage i d hclosed y + y * derivationPreimage i d hclosed x)
    simp only [derivationPreimage_spec, map_mul, map_add, d.leibniz, smul_eq_mul]

@[simp] theorem injectiveDerivationPullback_spec (x : F) :
    i (injectiveDerivationPullback i hi d hclosed x) = d (i x) :=
  derivationPreimage_spec i d hclosed x

end Pullback

section FractionClosure
variable {R F L : Type*} [CommRing R] [Field F] [Field L]
  [Algebra R F] [IsFractionRing R F] [Algebra ℤ L]

/-- Compatibility on the base ring proves derivative closure of the entire
fraction-field image, with an explicit quotient-rule preimage. -/
theorem fraction_image_derivative_closed
    (i : F →+* L) (d : Derivation ℤ L L) (D : R → R)
    (hcomp : ∀ r : R, d (i (algebraMap R F r)) = i (algebraMap R F (D r))) :
    ∀ x : F, ∃ y : F, i y = d (i x) := by
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A:=R) x
  refine ⟨(algebraMap R F (D a) * algebraMap R F b -
    algebraMap R F a * algebraMap R F (D b)) / (algebraMap R F b)^2, ?_⟩
  simp only [map_div₀]
  rw [Derivation.leibniz_div (R:=ℤ) (M:=L) d, hcomp, hcomp]
  simp only [map_div₀, map_sub, map_mul, map_pow, smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

end FractionClosure
end StrictEUnit

#print axioms StrictEUnit.derivationPreimage
#print axioms StrictEUnit.derivationPreimage_spec
#print axioms StrictEUnit.derivationPreimageAddHom
#print axioms StrictEUnit.injectiveDerivationPullback
#print axioms StrictEUnit.injectiveDerivationPullback_spec
#print axioms StrictEUnit.fraction_image_derivative_closed
