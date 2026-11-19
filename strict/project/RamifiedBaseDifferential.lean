import RamifiedBaseMatrix

/-! The actual differential equation of the constructed ramified base unit.
D = N times the manuscript derivation, so D(t)=t and D(ell)=N. -/
noncomputable section
namespace StrictEUnit
variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

/-- The manuscript's Laurent Euler normalization after ramification. -/
def ramifiedBaseDerivation (N : ℕ) : Derivation k (LaurentLogBase k) (LaurentLogBase k) :=
  (N : k) • manuscriptBaseDerivation N

@[simp] theorem ramifiedBaseDerivation_coeff (N : ℕ) (hN : N ≠ 0)
    (p : LaurentLogBase k) (j : ℕ) (a : ℤ) :
    ((ramifiedBaseDerivation N p).coeff j) a =
      (N : k) * ((p.coeff (j+1)) a * (j+1:k)) + (a:k) * (p.coeff j) a := by
  have hNk : (N:k) ≠ 0 := Nat.cast_ne_zero.mpr hN
  change (N:k) * ((manuscriptBaseDerivation N p).coeff j) a = _
  rw [manuscriptBaseDerivation_coeff, mul_add]
  congr 1
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hNk, one_mul]

@[simp] theorem ramifiedBaseDerivation_X (N : ℕ) (hN : N ≠ 0) :
    ramifiedBaseDerivation (k := k) N Polynomial.X = algebraMap k (LaurentLogBase k) (N:k) := by
  apply Polynomial.ext
  intro j
  apply LaurentPolynomial.ext
  intro a
  rw [ramifiedBaseDerivation_coeff N hN]
  simp only [Polynomial.coeff_X, Polynomial.algebraMap_apply, Polynomial.coeff_C]
  by_cases hj : j = 0
  · subst j
    simp only [Nat.zero_add, Nat.cast_one, if_true, mul_one, one_ne_zero, if_false,
      Finsupp.zero_apply, mul_zero, add_zero]
    simp only [Nat.cast_zero, zero_add, mul_one]
    rw [← LaurentPolynomial.C_eq_algebraMap]
    change (N:k) * (1 : LaurentPolynomial k) a = (LaurentPolynomial.C (N:k)) a
    change (N:k) * (Finsupp.single (0:ℤ) (1:k)) a = (Finsupp.single (0:ℤ) (N:k)) a
    by_cases ha : (0:ℤ) = a <;>
      simp only [Finsupp.single_apply, ha, if_true, if_false, mul_one, mul_zero]
  · have hj1 : ¬ 1 = j + 1 := by omega
    simp only [hj1, if_false, Finsupp.zero_apply, zero_mul, mul_zero, hj, zero_add]
    by_cases hjone : 1 = j
    · subst j
      simp only [if_true]
      change (a:k) * (1 : LaurentPolynomial k) a = 0
      by_cases ha : a = 0
      · subst a; simp only [Int.cast_zero, zero_mul]
      · change (a:k) * (Finsupp.single (0:ℤ) (1:k)) a = 0
        simp only [Finsupp.single_apply, Ne.symm ha, if_false, mul_zero]
    · simp [hjone]

@[simp] theorem ramifiedBaseDerivation_T (N : ℕ) (hN : N ≠ 0) (a : ℤ) :
    ramifiedBaseDerivation (k := k) N (Polynomial.C (LaurentPolynomial.T a)) =
      (a:k) • Polynomial.C (LaurentPolynomial.T a) := by
  apply Polynomial.ext
  intro j
  apply LaurentPolynomial.ext
  intro b
  rw [ramifiedBaseDerivation_coeff N hN]
  simp only [Polynomial.coeff_C, Polynomial.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Finsupp.zero_apply,
    zero_mul, mul_zero, zero_add]
  by_cases hj : j = 0
  · simp only [hj, if_true]
    change (b:k) * (Finsupp.single a (1:k)) b = (a:k) * (Finsupp.single a (1:k)) b
    by_cases hab : a = b
    · subst b; rfl
    · simp [Finsupp.single_apply, hab]
  · simp [hj]

/-- Integer Euler weights as an actual constant diagonal matrix. -/
def ramifiedWeightMatrix (m : n → ℤ) : Matrix n n (LaurentLogBase k) :=
  Matrix.diagonal fun i => algebraMap k (LaurentLogBase k) (m i : k)

theorem ramifiedWeightUnit_derivative (N : ℕ) (hN : N ≠ 0) (m : n → ℤ) :
    matrixDerivative (ramifiedBaseDerivation (k := k) N)
      (ramifiedWeightUnit (k := k) m : Matrix n n (LaurentLogBase k)) =
      ramifiedWeightMatrix m * (ramifiedWeightUnit (k := k) m : Matrix n n (LaurentLogBase k)) := by
  apply Matrix.ext
  intro i j
  change ramifiedBaseDerivation N
    (Matrix.diagonal (fun i => (Polynomial.C (LaurentPolynomial.T (m i)) : LaurentLogBase k)) i j) = _
  change _ = (Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) (m i : k)) *
    Matrix.diagonal (fun i => (Polynomial.C (LaurentPolynomial.T (m i)) : LaurentLogBase k))) i j
  rw [Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, ramifiedBaseDerivation_T N hN, Algebra.smul_def]
  · simp only [Matrix.diagonal_apply_ne _ hij, map_zero, mul_zero]

theorem ramifiedLogUnit_derivative (N : ℕ) (hN : N ≠ 0)
    (J : Matrix n n k) (hJ : IsNilpotent J) :
    matrixDerivative (ramifiedBaseDerivation (k := k) N)
      (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k)) =
      (N:k) • (ramifiedConstantMatrix J * (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k))) := by
  change matrixDerivative (ramifiedBaseDerivation N)
    (IsNilpotent.exp (Polynomial.X • (algebraMap k (LaurentLogBase k)).mapMatrix J)) = _
  rw [matrixDerivative_nilpotent_exp _ _ _ hJ, ramifiedBaseDerivation_X N hN]
  change algebraMap k (LaurentLogBase k) (N:k) • _ = (N:k) • _
  exact algebraMap_smul _ _ _

/-- The support condition records commutation of the nilpotent part with
integer weights, rather than postulating commutation with a variable matrix. -/
def RespectsRamifiedWeights (m : n → ℤ) (J : Matrix n n k) : Prop :=
  ∀ i j, m i ≠ m j → J i j = 0

/-- In characteristic zero the support condition is precisely commutation
with the constant diagonal integer-weight matrix. -/
theorem respectsRamifiedWeights_iff_commute (m : n → ℤ) (J : Matrix n n k) :
    RespectsRamifiedWeights m J ↔ Commute (Matrix.diagonal fun i => (m i : k)) J := by
  constructor
  · intro h
    change Matrix.diagonal _ * J = J * Matrix.diagonal _
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : m i = m j
    · rw [hij, mul_comm]
    · rw [h i j hij, mul_zero, zero_mul]
  · intro h i j hij
    by_contra hJij
    have he := congrArg (fun A : Matrix n n k => A i j) h.eq
    dsimp only at he
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (J i j)] at he
    have hc : (m i : k) = (m j : k) := mul_right_cancel₀ hJij he
    exact hij (Int.cast_injective hc)

omit [CharZero k] in
theorem ramifiedWeightUnit_commutes (m : n → ℤ) (J : Matrix n n k)
    (hweight : RespectsRamifiedWeights m J) :
    Commute (ramifiedWeightUnit (k := k) m : Matrix n n (LaurentLogBase k))
      (ramifiedConstantMatrix J) := by
  change Matrix.diagonal _ * ramifiedConstantMatrix J = ramifiedConstantMatrix J * Matrix.diagonal _
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : m i = m j
  · rw [hij, mul_comm]
  · change _ * algebraMap k (LaurentLogBase k) (J i j) = algebraMap k (LaurentLogBase k) (J i j) * _
    rw [hweight i j hij, map_zero, mul_zero, zero_mul]

/-- The constructed unit is a fundamental solution of the constant regular-
singular matrix equation. Its ODE is a conclusion, not an input. -/
theorem ramifiedBaseMatrix_derivative (N : ℕ) (hN : N ≠ 0)
    (m : n → ℤ) (J : Matrix n n k) (hJ : IsNilpotent J)
    (hweight : RespectsRamifiedWeights m J) :
    matrixDerivative (ramifiedBaseDerivation (k := k) N)
      (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) =
      (ramifiedWeightMatrix m + (N:k) • ramifiedConstantMatrix J) *
        (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) := by
  change matrixDerivative (ramifiedBaseDerivation N)
      ((ramifiedWeightUnit (k := k) m : Matrix n n (LaurentLogBase k)) *
        (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k))) = _
  rw [matrixDerivative_mul, ramifiedWeightUnit_derivative N hN,
    ramifiedLogUnit_derivative N hN]
  change _ = (ramifiedWeightMatrix m + (N:k) • ramifiedConstantMatrix J) *
    ((ramifiedWeightUnit (k := k) m : Matrix n n (LaurentLogBase k)) *
      (ramifiedLogUnit J hJ : Matrix n n (LaurentLogBase k)))
  rw [add_mul, Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc,
    ← mul_assoc, (ramifiedWeightUnit_commutes m J hweight).eq]
  rw [mul_assoc (ramifiedConstantMatrix J)]

end StrictEUnit
