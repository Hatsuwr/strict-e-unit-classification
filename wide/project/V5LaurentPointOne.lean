import V5MixedPointedFiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Polynomial.Div

open scoped TensorProduct
noncomputable section
namespace StrictEUnit
set_option maxHeartbeats 400000
attribute [-instance] TensorProduct.leftModule
variable {k : Type*} [Field k]

def v5LaurentPointOne : LaurentPolynomial k →ₐ[k] k where
  __ := LaurentPolynomial.eval₂ (RingHom.id k) 1
  commutes' c := LaurentPolynomial.eval₂_C _ _ c

theorem v5LaurentPointOne_kernel :
    RingHom.ker (v5LaurentPointOne (k := k)).toRingHom =
      Ideal.span {LaurentPolynomial.T 1 - (1 : LaurentPolynomial k)} := by
  apply le_antisymm
  · intro p hp
    change v5LaurentPointOne p = 0 at hp
    induction p using LaurentPolynomial.induction_on_mul_T with
    | Qf =>
      rename_i p n
      have he : p.eval 1 = 0 := by
        simpa [v5LaurentPointOne, LaurentPolynomial.eval₂_toLaurent,
          LaurentPolynomial.eval₂_T_neg_n] using hp
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr he
      rw [Ideal.mem_span_singleton]
      refine ⟨q.toLaurent * LaurentPolynomial.T (-(n : ℤ)), ?_⟩
      rw [hq, map_mul, map_sub]
      simp only [Polynomial.toLaurent_X, Polynomial.toLaurent_C, map_one]
      ring
  · apply Ideal.span_le.mpr
    rintro p rfl
    change v5LaurentPointOne (LaurentPolynomial.T 1 - (1 : LaurentPolynomial k)) = 0
    simp [v5LaurentPointOne]

/-- Tensor fiber at z=1 is the quotient by the literal coordinate minus 1. -/
def v5LaurentPointOneQuotient {S : Type*} [CommRing S] [Algebra (LaurentPolynomial k) S] :
    letI : Algebra (LaurentPolynomial k) k := (v5LaurentPointOne (k := k)).toRingHom.toAlgebra
    (S ⧸ Ideal.span {algebraMap (LaurentPolynomial k) S (LaurentPolynomial.T 1) - 1}) ≃+*
      k ⊗[LaurentPolynomial k] S := by
  letI : Algebra (LaurentPolynomial k) k := (v5LaurentPointOne (k := k)).toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap (LaurentPolynomial k) k) := by
    intro a
    refine ⟨LaurentPolynomial.C a, ?_⟩
    exact LaurentPolynomial.eval₂_C _ _ a
  let q : (LaurentPolynomial k ⧸ RingHom.ker (algebraMap (LaurentPolynomial k) k)) ≃ₐ[LaurentPolynomial k] k :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId (LaurentPolynomial k) k) hsurj
  have hi : Ideal.map (algebraMap (LaurentPolynomial k) S)
      (RingHom.ker (algebraMap (LaurentPolynomial k) k)) =
      Ideal.span {algebraMap (LaurentPolynomial k) S (LaurentPolynomial.T 1) - 1} := by
    change Ideal.map _ (RingHom.ker (v5LaurentPointOne (k := k)).toRingHom) = _
    rw [v5LaurentPointOne_kernel, Ideal.map_span]
    simp only [Set.image_singleton, map_sub, map_one]
  exact (Ideal.quotEquivOfEq hi.symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (RingHom.ker (algebraMap (LaurentPolynomial k) k))).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S)) q).toRingEquiv.trans
        (Algebra.TensorProduct.comm (LaurentPolynomial k) S k).toRingEquiv))

@[simp] theorem v5LaurentPointOneQuotient_mk {S : Type*} [CommRing S]
    [Algebra (LaurentPolynomial k) S] (s : S) :
    letI : Algebra (LaurentPolynomial k) k := (v5LaurentPointOne (k := k)).toRingHom.toAlgebra
    v5LaurentPointOneQuotient (k := k) (S := S) (Ideal.Quotient.mk _ s) =
      (1 : k) ⊗ₜ[LaurentPolynomial k] s := by
  simp [v5LaurentPointOneQuotient]


end StrictEUnit
#print axioms StrictEUnit.v5LaurentPointOne_kernel
#print axioms StrictEUnit.v5LaurentPointOneQuotient

#print axioms StrictEUnit.v5LaurentPointOneQuotient_mk
