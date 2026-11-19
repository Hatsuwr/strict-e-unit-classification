import V5MeromorphicZero
import V5MarkedKummerFactor
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

variable {k : Type*} [Field k] [Algebra k ℂ]

def v5MeromorphicPowerPullback (q : ℕ) :
    v5MeromorphicZeroAlgebra k →ₐ[k] v5MeromorphicZeroAlgebra k where
  toFun f := ⟨fun z => f.val (z^q), f.property.pullback q⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The Kummer power map gives matching images for the two Laurent scalar maps. -/
theorem v5MeromorphicPowerPullback_base (q : ℕ) (p : LaurentPolynomial k) :
    v5MeromorphicPowerPullback (k := k) q (v5MeromorphicZeroLaurent k p) =
      v5MeromorphicZeroLaurent k (v5LaurentPower q p) := by
  apply Subtype.ext
  funext z
  change (v5MeromorphicZeroLaurent k p).val (z^q) = _
  rw [v5MeromorphicZeroLaurent_apply, v5MeromorphicZeroLaurent_apply]
  exact (v5LaurentPower_eval (algebraMap k ℂ) q z p).symm

/-- Any two compatible Laurent-base maps to punctured meromorphic functions yield
a genuine tensor-ring realization. Its pure-tensor evaluation is pointwise. -/
theorem v5_meromorphic_tensor_realization {S D : Type*} [CommRing S] [CommRing D]
    [Algebra (LaurentPolynomial k) S] [Algebra (LaurentPolynomial k) D]
    (β : S →+* v5MeromorphicZeroAlgebra k) (ω : D →+* v5MeromorphicZeroAlgebra k)
    (hβω : β.comp (algebraMap (LaurentPolynomial k) S) =
      ω.comp (algebraMap (LaurentPolynomial k) D)) :
    ∃ η : S ⊗[LaurentPolynomial k] D →+* v5MeromorphicZeroAlgebra k,
      ∀ s d z, (η (s ⊗ₜ[LaurentPolynomial k] d)).val z = (β s).val z * (ω d).val z := by
  letI : Algebra (LaurentPolynomial k) (v5MeromorphicZeroAlgebra k) :=
    (ω.comp (algebraMap (LaurentPolynomial k) D)).toAlgebra
  let β' : S →ₐ[LaurentPolynomial k] v5MeromorphicZeroAlgebra k :=
    { β with commutes' := fun p => DFunLike.congr_fun hβω p }
  let ω' : D →ₐ[LaurentPolynomial k] v5MeromorphicZeroAlgebra k :=
    { ω with commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift β' ω' (fun _ _ => Commute.all _ _)).toRingHom, ?_⟩
  intro s d z
  change ((Algebra.TensorProduct.lift β' ω' (fun _ _ => Commute.all _ _))
    (s ⊗ₜ[LaurentPolynomial k] d)).val z = _
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

/-- Specialization to the Kummer-adapted left and right maps, packaged with
preservation of the chosen mark for all pure tensors. -/
theorem v5_kummer_meromorphic_tensor {S D : Type*} [CommRing S] [CommRing D]
    [Algebra (LaurentPolynomial k) S] [Algebra (LaurentPolynomial k) D]
    (q : ℕ) (β : S →+* v5MeromorphicZeroAlgebra k) (ω : D →+* LaurentPolynomial k)
    (hβ : ∀ p, β (algebraMap (LaurentPolynomial k) S p) = v5MeromorphicZeroLaurent k p)
    (hω : ∀ p, ω (algebraMap (LaurentPolynomial k) D p) = v5LaurentPower q p) :
    ∃ η : S ⊗[LaurentPolynomial k] D →+* v5MeromorphicZeroAlgebra k,
      (∀ s d z, (η (s ⊗ₜ[LaurentPolynomial k] d)).val z = (β s).val (z^q) *
        LaurentPolynomial.eval₂ (algebraMap k ℂ) z (ω d)) ∧
      (∀ s d, (η (s ⊗ₜ[LaurentPolynomial k] d)).val 1 = (β s).val 1 *
        LaurentPolynomial.eval₂ (algebraMap k ℂ) 1 (ω d)) := by
  let β' := (v5MeromorphicPowerPullback q).toRingHom.comp β
  let ω' := (v5MeromorphicZeroLaurent k).toRingHom.comp ω
  have hb : β'.comp (algebraMap (LaurentPolynomial k) S) =
      ω'.comp (algebraMap (LaurentPolynomial k) D) := by
    apply RingHom.ext
    intro p
    change v5MeromorphicPowerPullback q (β (algebraMap (LaurentPolynomial k) S p)) =
      v5MeromorphicZeroLaurent k (ω (algebraMap (LaurentPolynomial k) D p))
    rw [hβ, hω, v5MeromorphicPowerPullback_base]
  obtain ⟨η, hη⟩ := v5_meromorphic_tensor_realization β' ω' hb
  have hη' s d z : (η (s ⊗ₜ[LaurentPolynomial k] d)).val z =
      (β s).val (z^q) * LaurentPolynomial.eval₂ (algebraMap k ℂ) z (ω d) := by
    rw [hη]
    change (β s).val (z^q) * (v5MeromorphicZeroLaurent k (ω d)).val z = _
    rw [v5MeromorphicZeroLaurent_apply]
  exact ⟨η, hη', fun s d => by simpa only [one_pow] using hη' s d 1⟩

end StrictEUnit
#print axioms StrictEUnit.v5MeromorphicPowerPullback_base
#print axioms StrictEUnit.v5_meromorphic_tensor_realization
#print axioms StrictEUnit.v5_kummer_meromorphic_tensor
