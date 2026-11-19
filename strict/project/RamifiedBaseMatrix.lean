import ManuscriptBaseSimplicity
import LaurentLogBasePoint
import NilpotentMatrixExpDerivative
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An actual ramified regular-singular base unit, constructed from integer
weights and a nilpotent constant matrix. No Jordan decomposition, analytic
realization, or existence of an André frame is asserted here. -/
noncomputable section
namespace StrictEUnit
variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

/-- Constant matrices embedded into the finite Laurent-log polynomial ring. -/
def ramifiedConstantMatrix (J : Matrix n n k) : Matrix n n (LaurentLogBase k) :=
  (algebraMap k (LaurentLogBase k)).mapMatrix J

/-- The integral torus factor, with its explicit inverse. -/
def ramifiedWeightUnit (m : n → ℤ) : (Matrix n n (LaurentLogBase k))ˣ where
  val := Matrix.diagonal fun i => Polynomial.C (LaurentPolynomial.T (m i))
  inv := Matrix.diagonal fun i => Polynomial.C (LaurentPolynomial.T (-m i))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, map_one, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [← map_mul, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, map_one, Matrix.diagonal_one]

/-- The nilpotent logarithm exponent is a genuine matrix over B. -/
def ramifiedLogExponent (J : Matrix n n k) : Matrix n n (LaurentLogBase k) :=
  (Polynomial.X : LaurentLogBase k) • ramifiedConstantMatrix J

omit [CharZero k] in
theorem ramifiedLogExponent_nilpotent (J : Matrix n n k) (hJ : IsNilpotent J) :
    IsNilpotent (ramifiedLogExponent J) :=
  (hJ.map (algebraMap k (LaurentLogBase k)).mapMatrix).smul Polynomial.X

/-- The finite logarithmic exponential, with exp(-ell J) as actual inverse. -/
def ramifiedLogUnit (J : Matrix n n k) (hJ : IsNilpotent J) :
    (Matrix n n (LaurentLogBase k))ˣ where
  val := IsNilpotent.exp (ramifiedLogExponent J)
  inv := IsNilpotent.exp (-ramifiedLogExponent J)
  val_inv := (ramifiedLogExponent_nilpotent J hJ).exp_mul_exp_neg_self
  inv_val := (ramifiedLogExponent_nilpotent J hJ).exp_neg_mul_exp_self

/-- Z = diag(t^m) exp(ell J), constructed rather than assumed. -/
def ramifiedBaseMatrix (m : n → ℤ) (J : Matrix n n k) (hJ : IsNilpotent J) :
    (Matrix n n (LaurentLogBase k))ˣ := ramifiedWeightUnit m * ramifiedLogUnit J hJ

@[simp] theorem ramifiedBaseMatrix_val (m : n → ℤ) (J : Matrix n n k)
    (hJ : IsNilpotent J) :
    (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) =
      Matrix.diagonal (fun i => Polynomial.C (LaurentPolynomial.T (m i))) *
        IsNilpotent.exp (ramifiedLogExponent J) := rfl

@[simp] theorem ramifiedBaseMatrix_inv (m : n → ℤ) (J : Matrix n n k)
    (hJ : IsNilpotent J) :
    (↑(ramifiedBaseMatrix m J hJ)⁻¹ : Matrix n n (LaurentLogBase k)) =
      IsNilpotent.exp (-ramifiedLogExponent J) *
        Matrix.diagonal (fun i => Polynomial.C (LaurentPolynomial.T (-m i))) := rfl

/-- For every supplied nilpotence bound, the constructed exponential is the
ordinary truncated exponential polynomial, with no infinite series. -/
theorem ramifiedLogUnit_eq_sum (J : Matrix n n k) (hJ : IsNilpotent J)
    (q : ℕ) (hq : J ^ q = 0) :
    (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k)) =
      ∑ r ∈ Finset.range q, (r.factorial : ℚ)⁻¹ •
        ((Polynomial.X : LaurentLogBase k) ^ r • ramifiedConstantMatrix (J ^ r)) := by
  have hp : ramifiedLogExponent J ^ q = 0 := by
    simp only [ramifiedLogExponent, smul_pow, ramifiedConstantMatrix,
      ← map_pow, hq, map_zero, smul_zero]
  change IsNilpotent.exp (ramifiedLogExponent J) = _
  rw [IsNilpotent.exp_eq_sum hp]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [ramifiedLogExponent, smul_pow, ramifiedConstantMatrix, map_pow]

theorem ramifiedBaseMatrix_det_isUnit (m : n → ℤ) (J : Matrix n n k)
    (hJ : IsNilpotent J) :
    IsUnit (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)).det :=
  Matrix.isUnits_det_units _

/-- Evaluation at ell = 0 of the logarithm factor is the identity. -/
theorem ramifiedLogUnit_eval_zero (J : Matrix n n k) (hJ : IsNilpotent J) :
    (Polynomial.evalRingHom (0 : LaurentPolynomial k)).mapMatrix
      (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k)) = 1 := by
  change (Polynomial.evalRingHom (0 : LaurentPolynomial k)).mapMatrix
    (IsNilpotent.exp (ramifiedLogExponent J)) = 1
  rw [(ramifiedLogExponent_nilpotent J hJ).map_exp]
  have hx : (Polynomial.evalRingHom (0 : LaurentPolynomial k)).mapMatrix
      (ramifiedLogExponent J) = 0 := by
    ext i j
    simp [ramifiedLogExponent, ramifiedConstantMatrix, smul_eq_mul]
  rw [hx, IsNilpotent.exp_zero]

/-- The determinant of the logarithm factor is exactly one. The proof uses
polynomial units and evaluation, rather than an assumed trace formula. -/
theorem ramifiedLogUnit_det (J : Matrix n n k) (hJ : IsNilpotent J) :
    (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k)).det = 1 := by
  obtain ⟨p, hp, hCp⟩ := Polynomial.isUnit_iff.mp
    (Matrix.isUnits_det_units (ramifiedLogUnit J hJ))
  have he := congrArg Matrix.det (ramifiedLogUnit_eval_zero J hJ)
  rw [← RingHom.map_det, Matrix.det_one, ← hCp] at he
  have hp1 : p = 1 := by simpa using he
  rw [← hCp, hp1, map_one]

/-- Its determinant is the actual invertible Laurent monomial t^(sum m_i). -/
theorem ramifiedBaseMatrix_det (m : n → ℤ) (J : Matrix n n k)
    (hJ : IsNilpotent J) :
    (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)).det =
      Polynomial.C (LaurentPolynomial.T (∑ i, m i)) := by
  change ((ramifiedWeightUnit (k := k) m : Matrix n n (LaurentLogBase k)) *
    (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k))).det = _
  rw [Matrix.det_mul, ramifiedLogUnit_det, mul_one]
  change (Matrix.diagonal fun i => (Polynomial.C (LaurentPolynomial.T (m i)) : LaurentLogBase k)).det = _
  rw [Matrix.det_diagonal]
  have h (s : Finset n) : ∏ i ∈ s, (Polynomial.C (LaurentPolynomial.T (m i)) : LaurentLogBase k) =
      Polynomial.C (LaurentPolynomial.T (∑ i ∈ s, m i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        LaurentPolynomial.T_add, map_mul]
  exact h Finset.univ

/-- At the specified algebraic base point t=1, ell=0, Z is exactly I. -/
theorem ramifiedBaseMatrix_at_point (m : n → ℤ) (J : Matrix n n k)
    (hJ : IsNilpotent J) :
    (laurentLogBasePoint k).toRingHom.mapMatrix
      (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) = 1 := by
  rw [ramifiedBaseMatrix_val, map_mul]
  have hw : (laurentLogBasePoint k).toRingHom.mapMatrix
      (Matrix.diagonal fun i => Polynomial.C (LaurentPolynomial.T (m i))) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      change laurentLogBasePoint k (Polynomial.C (LaurentPolynomial.T (m i))) = 1
      exact laurentLogBasePoint_monomial k (m i) 1
    · simp [Matrix.diagonal_apply, hij]
  rw [hw, one_mul, (ramifiedLogExponent_nilpotent J hJ).map_exp]
  have hx : (laurentLogBasePoint k).toRingHom.mapMatrix (ramifiedLogExponent J) = 0 := by
    ext i j
    simp [ramifiedLogExponent, smul_eq_mul]
  rw [hx, IsNilpotent.exp_zero]

end StrictEUnit
