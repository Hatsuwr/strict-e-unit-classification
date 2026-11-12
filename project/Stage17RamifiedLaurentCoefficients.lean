import Stage17FormalEulerTaylor
import FormalMatrixLogRemoval

/-! Literal ramification of finite Laurent coefficients and the actual Taylor
image of polynomial evaluation. No coefficient matrix is supplied in the formal
ambient field. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

/-- The positive-coordinate Laurent monomial as an actual ring unit. -/
def stage17_laurentCoordinateUnit (k : Type*) [Field k] : (LaurentPolynomial k)ˣ :=
  (LaurentPolynomial.isUnit_T (R := k) 1).unit

@[simp] theorem stage17_laurentCoordinateUnit_val (k : Type*) [Field k] :
    (stage17_laurentCoordinateUnit k : LaurentPolynomial k) = LaurentPolynomial.T 1 :=
  (LaurentPolynomial.isUnit_T (R := k) 1).unit_spec

/-- Actual substitution t ↦ t^N on finite Laurent polynomials. -/
def stage17_laurentPowerPullback (k : Type*) [Field k] (N : ℕ) :
    LaurentPolynomial k →+* LaurentPolynomial k :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C (stage17_laurentCoordinateUnit k ^ N)

/-- The ramified coefficient lives in the precise finite Laurent-log base. -/
def stage17_laurentBasePullback (k : Type*) [Field k] (N : ℕ) :
    LaurentPolynomial k →+* LaurentLogBase k :=
  Polynomial.C.comp (stage17_laurentPowerPullback k N)

/-- Its literal inclusion into the established formal ambient field. -/
def stage17_laurentAmbientPullback (k : Type*) [Field k] (N : ℕ) :
    LaurentPolynomial k →+* RatFunc (LaurentSeries k) :=
  formalBaseEmbedding.toRingHom.comp (stage17_laurentBasePullback k N)

@[simp] theorem stage17_laurentAmbientPullback_C (k : Type*) [Field k]
    (N : ℕ) (a : k) :
    stage17_laurentAmbientPullback k N (LaurentPolynomial.C a) =
      algebraMap k (RatFunc (LaurentSeries k)) a := by
  change formalBaseEmbedding (Polynomial.C
    (LaurentPolynomial.eval₂ LaurentPolynomial.C (stage17_laurentCoordinateUnit k ^ N)
      (LaurentPolynomial.C a))) = _
  rw [LaurentPolynomial.eval₂_C]
  exact formalBaseEmbedding.commutes a

/-- The actual arithmetic coordinate pulls back to its ordinary Nth power. -/
theorem stage17_arithmeticPowerPullback_coordinate (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) :
    stage17_arithmeticPowerPullback k N hN (subfieldEntireCoordinate k) =
      subfieldEntireCoordinate k ^ N := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  rfl

/-- Compose the genuine arithmetic pullback with its genuine ambient Taylor map. -/
def stage17_ramifiedEntireFormalAlgHom (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0) :
    subfieldEntireFunctionAlgebra k →ₐ[k] RatFunc (LaurentSeries k) :=
  (stage17_entireFormalAlgHom k).comp (stage17_arithmeticPowerPullback k N hN)

/-- Finite Laurent substitution and the actual ramified coordinate have the
same image; this is the bridge used in polynomial denominator clearing. -/
theorem stage17_laurentAmbientPullback_coordinate (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) :
    stage17_laurentAmbientPullback k N (LaurentPolynomial.T 1) =
      stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) := by
  change formalBaseEmbedding (Polynomial.C
    (LaurentPolynomial.eval₂ LaurentPolynomial.C (stage17_laurentCoordinateUnit k ^ N)
      (LaurentPolynomial.T (1 : ℤ)))) = _
  rw [show (1 : ℤ) = (1 : ℕ) by rfl, LaurentPolynomial.eval₂_T_n]
  simp only [pow_one, Units.val_pow_eq_pow_val, stage17_laurentCoordinateUnit_val]
  rw [map_pow, map_pow, formalBaseEmbedding_C]
  change RatFunc.C (laurentPolynomialToSeries (LaurentPolynomial.T 1)) ^ N =
    stage17_entireFormalAlgHom k
      (stage17_arithmeticPowerPullback k N hN (subfieldEntireCoordinate k))
  rw [stage17_arithmeticPowerPullback_coordinate, map_pow,
    stage17_entireFormalAlgHom_apply, stage17_entireLaurent_coordinate]
  congr 2
  exact laurentPolynomialToSeries_single 1 1

/-- Actual polynomial evaluation maps to the same finite Laurent substitution. -/
theorem stage17_ramifiedEntireFormal_polynomial (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (p : Polynomial k) :
    stage17_ramifiedEntireFormalAlgHom k N hN
      (Polynomial.aeval (subfieldEntireCoordinate k) p) =
      stage17_laurentAmbientPullback k N (Polynomial.toLaurent p) := by
  let ns := @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)
  letI : Add (subfieldEntireFunctionAlgebra k) :=
    @AddZeroClass.toAdd _ (@AddMonoid.toAddZeroClass _
      (@AddCommMonoid.toAddMonoid _
        (@NonUnitalNonAssocSemiring.toAddCommMonoid _ ns)))
  letI : Mul (subfieldEntireFunctionAlgebra k) :=
    @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _ ns)
  letI : Module k (subfieldEntireFunctionAlgebra k) :=
    @Algebra.toModule k (subfieldEntireFunctionAlgebra k) inferInstance
      (subfieldEntireFunctionAlgebra k).toSemiring (subfieldEntireFunctionAlgebra k).algebra
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have ha : Polynomial.aeval (R := k) (subfieldEntireCoordinate k) (p + q) =
        Polynomial.aeval (R := k) (subfieldEntireCoordinate k) p +
          Polynomial.aeval (R := k) (subfieldEntireCoordinate k) q :=
      (Polynomial.aeval (R := k) (subfieldEntireCoordinate k)).map_add' p q
    have hb : stage17_ramifiedEntireFormalAlgHom k N hN
        (Polynomial.aeval (R := k) (subfieldEntireCoordinate k) p +
          Polynomial.aeval (R := k) (subfieldEntireCoordinate k) q) =
        stage17_ramifiedEntireFormalAlgHom k N hN
          (Polynomial.aeval (R := k) (subfieldEntireCoordinate k) p) +
        stage17_ramifiedEntireFormalAlgHom k N hN
          (Polynomial.aeval (R := k) (subfieldEntireCoordinate k) q) :=
      (stage17_ramifiedEntireFormalAlgHom k N hN).map_add' _ _
    have hc : Polynomial.toLaurent (p + q) =
        Polynomial.toLaurent p + Polynomial.toLaurent q :=
      (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k).map_add' p q
    have hd : stage17_laurentAmbientPullback k N
        (Polynomial.toLaurent p + Polynomial.toLaurent q) =
        stage17_laurentAmbientPullback k N (Polynomial.toLaurent p) +
          stage17_laurentAmbientPullback k N (Polynomial.toLaurent q) :=
      (stage17_laurentAmbientPullback k N).map_add' _ _
    rw [ha, hb, hc, hd, hp, hq]
  | monomial j a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      stage17_laurentAmbientPullback_C, stage17_laurentAmbientPullback_coordinate k N hN,
      AlgHom.commutes]

/-- Literal ramification sends t^L to the Lth power of the actual pulled coordinate. -/
theorem stage17_laurentAmbientPullback_T_nat (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (L : ℕ) :
    stage17_laurentAmbientPullback k N (LaurentPolynomial.T (L : ℤ)) =
      stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) ^ L := by
  rw [← Polynomial.toLaurent_X_pow, ← stage17_ramifiedEntireFormal_polynomial k N hN]
  simp only [map_pow, Polynomial.aeval_X]

/-- The pulled coordinate is nonzero, by the actual function value at one. -/
theorem stage17_ramifiedEntireFormal_coordinate_ne_zero (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) :
    stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) ≠ 0 := by
  intro h
  have hz := stage17_entireFormalAlgHom_injective k
    (h.trans (map_zero (stage17_entireFormalAlgHom k)).symm)
  have hv := congrArg (fun f : subfieldEntireFunctionAlgebra k => f.val.val 1) hz
  change (1 : ℂ) ^ N = 0 at hv
  exact one_ne_zero (by simpa only [one_pow] using hv)

end StrictEUnit
