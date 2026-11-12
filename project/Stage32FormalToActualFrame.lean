import Stage31RamifiedEntireInjectivity
import Stage17ArithmeticFrameODE

/-!
# Genuine formal-to-actual transport for arithmetic entire frames

The only differential premise is a literal equation in the established formal
ambient field. Finite Laurent denominators are cleared inside the actual
arithmetic entire-function algebra. Injectivity of its ramified Taylor map
then proves the cleared actual identity; evaluation and cancellation on
complex units recover the punctured analytic frame equation.

The scaled formal derivation is also proved to transport the actual ordinary
complex derivative. No analytic evaluation of arbitrary formal series, chosen
initial inverse, determinant hypothesis, or actual frame equation is assumed.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

local instance stage32EntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance stage32EntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring))

local instance stage32EntireAddGroup (k : Subfield ℂ) :
    AddGroup (subfieldEntireFunctionAlgebra k) :=
  @AddCommGroup.toAddGroup _
    (@Ring.toAddCommGroup _ (subfieldEntireFunctionAlgebra k).toRing)

private theorem algHom_cleared_frame_identity
    {k S Q I : Type*} [CommRing k] [CommRing S] [CommRing Q]
    [Algebra k S] [Algebra k Q] [Fintype I]
    (φ : S →ₐ[k] Q) (hφ : Function.Injective φ)
    (X d : S) (L : ℕ) (P f g : I → S) (B : I → Q) (M : I → k)
    (hP : ∀ l, φ (P l) = B l * (φ X)^L)
    (hd : φ d = (∑ l, B l * φ (f l)) -
      ∑ l, φ (g l) * algebraMap k Q (M l)) :
    X^L*d = (∑ l, P l*f l) - ∑ l, X^L*g l*algebraMap k S (M l) := by
  classical
  apply hφ
  simp only [map_mul, map_pow, map_sub, map_sum, AlgHom.commutes, hP]
  rw [hd, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro l hl
    ring
  · apply Finset.sum_congr rfl
    intro l hl
    ring

/-- Transparent canonical scaling; avoids concrete subfield instance-search expansion. -/
abbrev stage32_scaleFormalDerivation {k : Type*} [Field k]
    (c : RatFunc (LaurentSeries k))
    (D : Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k))) :
    Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)) := c • D

/-- Ordinary differentiation relative to the actual ramified coordinate. -/
def stage32_ramifiedOrdinaryDerivation (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0) :
    Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)) :=
  stage32_scaleFormalDerivation (k := k)
    ((stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))⁻¹)
    (formalAmbientDerivation (k := k) N hN)

/-- This is genuinely ordinary differentiation on the image of actual
arithmetic entire functions, not merely a chosen name for a derivation. -/
theorem stage32_ramifiedOrdinaryDerivation_transport
    (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) :
    stage32_ramifiedOrdinaryDerivation k N hN
        (stage17_ramifiedEntireFormalAlgHom k N hN f) =
      stage17_ramifiedEntireFormalAlgHom k N hN
        (subfieldEntireFunctionDerivation k f) := by
  change (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))⁻¹ *
    formalAmbientDerivation (k := k) N hN (stage17_ramifiedEntireFormalAlgHom k N hN f) = _
  have hd : formalAmbientDerivation (k := k) N hN
      (stage17_ramifiedEntireFormalAlgHom k N hN f) =
      stage17_ramifiedEntireFormalAlgHom k N hN
        (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k f) :=
    stage17_entireFormal_powerPullback_derivation k N hN f
  rw [hd, map_mul, ← mul_assoc,
    inv_mul_cancel₀ (stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN), one_mul]

/-- Every finite ordinary jet is transported by the same genuine map. -/
theorem stage32_ramifiedOrdinaryDerivation_iterate_transport
    (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) (a : ℕ) :
    ((stage32_ramifiedOrdinaryDerivation k N hN)^[a])
        (stage17_ramifiedEntireFormalAlgHom k N hN f) =
      stage17_ramifiedEntireFormalAlgHom k N hN
        (((subfieldEntireFunctionDerivation k)^[a]) f) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      stage32_ramifiedOrdinaryDerivation_transport]

variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- Laurent clearing converts the literal formal equation into an identity of
actual arithmetic entire functions by genuine Taylor injectivity. -/
theorem stage32_formalFrame_cleared_actual (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : matrixDerivative (formalAmbientDerivation (k := k) N hN) (stage17_formalFrame k N hN F) =
      B.map (stage17_laurentAmbientPullback k N) * stage17_formalFrame k N hN F -
      stage17_formalFrame k N hN F * M.map (algebraMap k (RatFunc (LaurentSeries k))))
    (L : ℕ) (P : Matrix n n (Polynomial k))
    (hP : ∀ i j, Polynomial.toLaurent (P i j) = B i j * LaurentPolynomial.T (L : ℤ))
    (i j : n) :
    subfieldEntireCoordinate k ^ L *
        (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (F i j)) =
      (∑ l, Polynomial.aeval (R := k) (subfieldEntireCoordinate k) (P i l) * F l j) -
        ∑ l, subfieldEntireCoordinate k ^ L * F i l *
          algebraMap k (subfieldEntireFunctionAlgebra k) (M l j) := by
  let φ := stage17_ramifiedEntireFormalAlgHom k N hN
  let x := φ (subfieldEntireCoordinate k)
  have hpoly (a b : n) :
      φ (Polynomial.aeval (R := k) (subfieldEntireCoordinate k) (P a b)) =
        stage17_laurentAmbientPullback k N (B a b) * x^L := by
    rw [stage17_ramifiedEntireFormal_polynomial, hP a b, map_mul,
      stage17_laurentAmbientPullback_T_nat k N hN]
  have hd : φ (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (F i j)) =
      formalAmbientDerivation (k := k) N hN (stage17_formalFrame k N hN F i j) :=
    (stage17_entireFormal_powerPullback_derivation k N hN (F i j)).symm
  have he := congrArg (fun A => A i j) hF
  change formalAmbientDerivation (k := k) N hN (stage17_formalFrame k N hN F i j) =
      (∑ l, stage17_laurentAmbientPullback k N (B i l) * φ (F l j)) -
        ∑ l, φ (F i l) * algebraMap k (RatFunc (LaurentSeries k)) (M l j) at he
  exact algHom_cleared_frame_identity φ
    (stage31_ramifiedEntireFormalAlgHom_injective k N hN)
    (subfieldEntireCoordinate k)
    (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (F i j)) L
    (fun l => Polynomial.aeval (R := k) (subfieldEntireCoordinate k) (P i l))
    (fun l => F l j) (fun l => F i l)
    (fun l => stage17_laurentAmbientPullback k N (B i l)) (fun l => M l j)
    (fun l => hpoly i l) (hd.trans he)

/-- The literal formal frame equation implies the actual punctured complex
Euler frame equation. Clearing is constructed, not supplied as a premise. -/
theorem stage32_actualEulerFrame_of_formalFrame_ode (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : matrixDerivative (formalAmbientDerivation (k := k) N hN) (stage17_formalFrame k N hN F) =
      B.map (stage17_laurentAmbientPullback k N) * stage17_formalFrame k N hN F -
      stage17_formalFrame k N hN F * M.map (algebraMap k (RatFunc (LaurentSeries k)))) :
    Stage17ActualEulerFrameRelation k B M F := by
  obtain ⟨L, _, P, hP⟩ := stage16_laurentMatrix_exists_positive_clearing B
  intro z i j
  have he := congrArg (stage14_subfieldEntireEvaluation k (z : ℂ))
    (stage32_formalFrame_cleared_actual k N hN B M F hF L P hP i j)
  rw [map_sub (stage14_subfieldEntireEvaluation k (z : ℂ))] at he
  simp only [map_mul, map_pow, map_sum,
    stage14_subfieldEntireEvaluation_polynomial, AlgHom.commutes] at he
  change (z : ℂ)^L * ((z : ℂ) * deriv (F i j).val.val (z : ℂ)) =
    (∑ l, (P i l).eval₂ k.subtype (z : ℂ) * (F l j).val.val (z : ℂ)) -
      ∑ l, (z : ℂ)^L * (F i l).val.val (z : ℂ) * (M l j : ℂ) at he
  apply mul_left_cancel₀ (pow_ne_zero L (Units.ne_zero z))
  rw [he, mul_sub, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : ℂ => a - b)
  · apply Finset.sum_congr rfl
    intro l _
    rw [stage17_laurent_clearing_evaluation k _ _ L (hP i l) z]
    ring
  · apply Finset.sum_congr rfl
    intro l _
    ring

/-- The genuine actual and ramified formal frame equations are equivalent. -/
theorem stage32_actualEulerFrame_iff_formalFrame_ode (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k)) :
    Stage17ActualEulerFrameRelation k B M F ↔
      matrixDerivative (formalAmbientDerivation (k := k) N hN) (stage17_formalFrame k N hN F) =
        B.map (stage17_laurentAmbientPullback k N) * stage17_formalFrame k N hN F -
        stage17_formalFrame k N hN F * M.map (algebraMap k (RatFunc (LaurentSeries k))) :=
  ⟨stage17_formalFrame_ode k N hN B M F,
    stage32_actualEulerFrame_of_formalFrame_ode k N hN B M F⟩

end StrictEUnit
