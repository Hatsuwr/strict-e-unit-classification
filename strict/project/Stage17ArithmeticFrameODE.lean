import Stage17RamifiedLaurentCoefficients
import Stage16LaurentMatrixClearing
import Stage16PuncturedEntireLocalization

/-!
# Actual Laurent frame equation to the formal ramified frame equation

The only differential hypothesis is the literal punctured analytic equation
z F′ = B(z) F - F M, with B an actual finite Laurent matrix over k. A common
polynomial denominator is constructed, the entire identity extends across zero,
and the genuine Taylor map transfers it before a nonzero monomial is canceled.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

local instance stage17FrameEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring))

local instance stage17FrameEntireAddGroup (k : Subfield ℂ) :
    AddGroup (subfieldEntireFunctionAlgebra k) :=
  @AddCommGroup.toAddGroup _
    (@Ring.toAddCommGroup _ (subfieldEntireFunctionAlgebra k).toRing)

/-- Actual entire functions are determined by their values at nonzero points. -/
theorem stage17_arithmeticEntire_eq_of_units (k : Subfield ℂ)
    (f g : subfieldEntireFunctionAlgebra k)
    (h : ∀ z : ℂˣ, stage14_subfieldEntireEvaluation k (z : ℂ) f =
      stage14_subfieldEntireEvaluation k (z : ℂ) g) : f = g := by
  apply stage16_entirePuncturedAlgHom_injective k
  funext z
  exact h (Units.mk0 z.val z.property)

/-- Generic-coefficient Laurent clearing agrees with actual complex evaluation. -/
theorem stage17_laurent_clearing_evaluation (k : Subfield ℂ)
    (b : LaurentPolynomial k) (p : Polynomial k) (L : ℕ)
    (hp : Polynomial.toLaurent p = b * LaurentPolynomial.T (L : ℤ)) (z : ℂˣ) :
    p.eval₂ k.subtype (z : ℂ) =
      (z : ℂ)^L * LaurentPolynomial.eval₂ k.subtype z b := by
  have h := congrArg (LaurentPolynomial.eval₂ k.subtype z) hp
  rw [LaurentPolynomial.eval₂_toLaurent, map_mul, LaurentPolynomial.eval₂_T_n] at h
  exact h.trans (mul_comm _ _)

variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual input relation. The Laurent coefficients are evaluated at units,
so this never evaluates a negative power at zero. -/
def Stage17ActualEulerFrameRelation
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k)) : Prop :=
  ∀ z : ℂˣ, ∀ i j,
    (z : ℂ) * deriv (F i j).val.val (z : ℂ) =
      (∑ l, LaurentPolynomial.eval₂ k.subtype z (B i l) * (F l j).val.val (z : ℂ)) -
        ∑ l, (F i l).val.val (z : ℂ) * (M l j : ℂ)

/-- Every actual Laurent frame relation has a denominator-cleared identity in
the actual arithmetic entire-function algebra, including the origin. -/
theorem stage17_actualEulerFrame_cleared
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (L : ℕ) (P : Matrix n n (Polynomial k))
    (hP : ∀ i j, Polynomial.toLaurent (P i j) = B i j * LaurentPolynomial.T (L : ℤ))
    (i j : n) :
    subfieldEntireCoordinate k ^ L *
        (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (F i j)) =
      (∑ l, Polynomial.aeval (subfieldEntireCoordinate k) (P i l) * F l j) -
        ∑ l, subfieldEntireCoordinate k ^ L * F i l *
          algebraMap k (subfieldEntireFunctionAlgebra k) (M l j) := by
  apply stage17_arithmeticEntire_eq_of_units k
  intro z
  rw [map_sub (stage14_subfieldEntireEvaluation k (z : ℂ))]
  simp only [map_mul, map_pow, map_sum,
    stage14_subfieldEntireEvaluation_polynomial, AlgHom.commutes]
  change (z : ℂ)^L * ((z : ℂ) * deriv (F i j).val.val (z : ℂ)) =
    (∑ l, (P i l).eval₂ k.subtype (z : ℂ) * (F l j).val.val (z : ℂ)) -
      ∑ l, (z : ℂ)^L * (F i l).val.val (z : ℂ) * (M l j : ℂ)
  rw [hF z i j, mul_sub, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : ℂ => a - b)
  · apply Finset.sum_congr rfl
    intro l _
    rw [stage17_laurent_clearing_evaluation k _ _ L (hP i l) z]
    ring
  · apply Finset.sum_congr rfl
    intro l _
    ring

/-- Entrywise ramified formal Taylor matrix of the actual arithmetic frame. -/
def stage17_formalFrame (N : ℕ) (hN : N ≠ 0)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k)) :
    Matrix n n (RatFunc (LaurentSeries k)) :=
  F.map (stage17_ramifiedEntireFormalAlgHom k N hN)

/-- Exact scalar ODE transfer, with Laurent coefficients constructed from B. -/
theorem stage17_formalFrame_entry_ode (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) (i j : n) :
    formalAmbientDerivation N hN (stage17_formalFrame k N hN F i j) =
      (∑ l, stage17_laurentAmbientPullback k N (B i l) *
        stage17_formalFrame k N hN F l j) -
      ∑ l, stage17_formalFrame k N hN F i l *
        algebraMap k (RatFunc (LaurentSeries k)) (M l j) := by
  obtain ⟨L, hL, P, hP⟩ := stage16_laurentMatrix_exists_positive_clearing B
  let φ := stage17_ramifiedEntireFormalAlgHom k N hN
  let x := φ (subfieldEntireCoordinate k)
  have hpoly (a b : n) :
      φ (Polynomial.aeval (subfieldEntireCoordinate k) (P a b)) =
        stage17_laurentAmbientPullback k N (B a b) * x^L := by
    rw [stage17_ramifiedEntireFormal_polynomial, hP a b, map_mul,
      stage17_laurentAmbientPullback_T_nat k N hN]
  have hd : φ (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (F i j)) =
      formalAmbientDerivation N hN (stage17_formalFrame k N hN F i j) :=
    (stage17_entireFormal_powerPullback_derivation k N hN (F i j)).symm
  -- Keep the Euler product grouped to use its analytic chain-rule transfer.
  have h' := congrArg φ (stage17_actualEulerFrame_cleared k B M F hF L P hP i j)
  rw [map_mul, map_pow, hd, map_sub φ, map_sum, map_sum] at h'
  simp only [map_mul, map_pow, AlgHom.commutes, hpoly] at h'
  apply mul_left_cancel₀ (pow_ne_zero L
    (stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN))
  change x^L * formalAmbientDerivation N hN (stage17_formalFrame k N hN F i j) = _
  rw [h', mul_sub, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : RatFunc (LaurentSeries k) => a - b)
  · apply Finset.sum_congr rfl
    intro l _
    change (_ * x^L) * φ (F l j) = x^L * (_ * φ (F l j))
    ring
  · apply Finset.sum_congr rfl
    intro l _
    change x^L * φ (F i l) * _ = x^L * (φ (F i l) * _)
    ring

/-- The original punctured analytic relation yields the full matrix ODE. -/
theorem stage17_formalFrame_ode (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    matrixDerivative (formalAmbientDerivation N hN) (stage17_formalFrame k N hN F) =
      B.map (stage17_laurentAmbientPullback k N) * stage17_formalFrame k N hN F -
      stage17_formalFrame k N hN F * M.map (algebraMap k (RatFunc (LaurentSeries k))) := by
  ext i j
  exact stage17_formalFrame_entry_ode k N hN B M F hF i j

end StrictEUnit
