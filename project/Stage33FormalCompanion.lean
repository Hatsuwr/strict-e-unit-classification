import Stage28LaurentCompanion
import Stage30ScalarJetIndependence
import Stage32FormalToActualFrame

/-! The exact finite Laurent Euler companion, after actual ramified pullback,
is the coordinate times the ordinary scalar companion. A supplied scalar ODE
therefore proves the Euler matrix equation for literal ordinary jet columns.
Neither a vector equation nor the existence of a scalar basis is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
local instance (k : Subfield ℂ) : SMul (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)) := ⟨(· * ·)⟩
local instance (k : Subfield ℂ) (m : ℕ) : SMul (RatFunc (LaurentSeries k))
    (Matrix (Fin m) (Fin m) (RatFunc (LaurentSeries k))) := ⟨fun c A i j => c * A i j⟩

/-- Actual polynomial pullback equals evaluation at the ramified coordinate. -/
theorem stage33_formal_polynomial_eval (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial k) :
    stage17_laurentAmbientPullback k N (Polynomial.toLaurent p) =
      Polynomial.aeval
        (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial i a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      stage17_laurentAmbientPullback_C, stage17_laurentAmbientPullback_coordinate k N hN]

/-- The leading coefficient is nonzero in the literal formal ambient field. -/
theorem stage33_formal_leading_ne_zero (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (m r : ℕ) (c : k) (p : Fin (m + 1) → Polynomial k)
    (hc : c ≠ 0) (hp : p (Fin.last m) = Polynomial.monomial r c) :
    Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))
        (p (Fin.last m)) ≠ 0 := by
  rw [hp, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  exact mul_ne_zero ((map_ne_zero (algebraMap k (RatFunc (LaurentSeries k)))).mpr hc)
    (pow_ne_zero r (stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN))

/-- The Laurent multiplier cancels the monomial at the actual formal coordinate. -/
theorem stage33_formal_leading_cancel (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (r : ℕ) (c : k) (hc : c ≠ 0) :
    (algebraMap k (RatFunc (LaurentSeries k)) c⁻¹ *
      stage17_laurentAmbientPullback k N (LaurentPolynomial.T (1 - (r : ℤ)))) *
      (algebraMap k (RatFunc (LaurentSeries k)) c *
        (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) ^ r) =
      stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) := by
  let x := stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)
  let ψ := stage17_laurentAmbientPullback k N
  have ht : ψ (LaurentPolynomial.T (1 - (r : ℤ))) * x ^ r = x := by
    rw [← stage17_laurentAmbientPullback_T_nat k N hN, ← map_mul,
      ← LaurentPolynomial.T_add, sub_add_cancel,
      stage17_laurentAmbientPullback_coordinate k N hN]
  calc
    _ = (algebraMap k (RatFunc (LaurentSeries k)) c⁻¹ *
          algebraMap k (RatFunc (LaurentSeries k)) c) *
        (ψ (LaurentPolynomial.T (1 - (r : ℤ))) * x ^ r) := by ring
    _ = x := by rw [← map_mul, inv_mul_cancel₀ hc, map_one, one_mul, ht]

/-- Exact identification of the pulled Laurent Euler and ordinary companions. -/
theorem stage33_formal_companion_eq (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (m r : ℕ) (c : k) (p : Fin (m + 1) → Polynomial k)
    (hc : c ≠ 0) (hp : p (Fin.last m) = Polynomial.monomial r c) :
    (stage28_laurentCompanion k m r c p).map (stage17_laurentAmbientPullback k N) =
      stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) •
        stage30_scalarCompanion m (fun j => Polynomial.aeval
          (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) (p j)) := by
  let x := stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)
  let a : Fin (m + 1) → RatFunc (LaurentSeries k) := fun j => Polynomial.aeval x (p j)
  let q := algebraMap k (RatFunc (LaurentSeries k)) c⁻¹ *
    stage17_laurentAmbientPullback k N (LaurentPolynomial.T (1 - (r : ℤ)))
  have ha : a (Fin.last m) ≠ 0 := stage33_formal_leading_ne_zero k N hN m r c p hc hp
  have hqa : q * a (Fin.last m) = x := by
    dsimp only [a]
    rw [hp, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact stage33_formal_leading_cancel k N hN r c hc
  have hq : q = x * (a (Fin.last m))⁻¹ := by
    rw [← hqa, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  ext i j
  simp only [Matrix.map_apply, stage28_laurentCompanion, Matrix.smul_apply,
    stage30_scalarCompanion, smul_eq_mul]
  split_ifs <;> simp only [map_zero, mul_zero, map_neg, map_mul,
    stage17_laurentAmbientPullback_coordinate k N hN, mul_one,
    stage17_laurentAmbientPullback_C, stage33_formal_polynomial_eval k N hN]
  · change -(q * a j.castSucc) = x * (-(a (Fin.last m))⁻¹ * a j.castSucc)
    rw [hq]
    ring

/-- A supplied scalar ODE proves the literal pulled-back Euler jet equation.
The ordinary derivation is the one proved to transport actual derivatives. -/
theorem stage33_formal_scalarJet_ode (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (m r : ℕ) (c : k) (p : Fin (m + 1) → Polynomial k)
    (hc : c ≠ 0) (hp : p (Fin.last m) = Polynomial.monomial r c)
    (y : Fin m → RatFunc (LaurentSeries k))
    (hy : ∀ j, ∑ l, Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) (p l) *
        ((stage32_ramifiedOrdinaryDerivation k N hN) :
          RatFunc (LaurentSeries k) → RatFunc (LaurentSeries k))^[l.val] (y j) = 0) :
    matrixDerivative (formalAmbientDerivation N hN)
      (Matrix.of (fun i j : Fin m =>
        stage30_derivativeJet (stage32_ramifiedOrdinaryDerivation k N hN) m (y j) i)) =
      (stage28_laurentCompanion k m r c p).map (stage17_laurentAmbientPullback k N) *
        (Matrix.of (fun i j : Fin m =>
          stage30_derivativeJet (stage32_ramifiedOrdinaryDerivation k N hN) m (y j) i)) := by
  let x := stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)
  let a : Fin (m + 1) → RatFunc (LaurentSeries k) := fun j => Polynomial.aeval x (p j)
  have hx : x ≠ 0 := stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN
  have ha : a (Fin.last m) ≠ 0 := stage33_formal_leading_ne_zero k N hN m r c p hc hp
  rw [stage33_formal_companion_eq k N hN m r c p hc hp]
  ext i j
  have h := stage30_derivativeJet_solution (stage32_ramifiedOrdinaryDerivation k N hN)
    m a ha (y j) (hy j) i
  have hxD (v : RatFunc (LaurentSeries k)) :
      formalAmbientDerivation N hN v = x * stage32_ramifiedOrdinaryDerivation k N hN v := by
    change _ = x * (x⁻¹ * formalAmbientDerivation N hN v)
    rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  simp only [matrixDerivative_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [hxD, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact (mul_assoc _ _ _).symm

end StrictEUnit
