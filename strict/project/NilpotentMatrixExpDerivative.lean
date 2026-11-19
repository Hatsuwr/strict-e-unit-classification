import FundamentalMatrixConstants
import Mathlib.RingTheory.Nilpotent.Exp

/-! Differentiating a genuine finite nilpotent matrix exponential. -/
noncomputable section
namespace StrictEUnit
variable {k R n : Type*} [CommRing k] [CommRing R]
  [Algebra k R] [Algebra ℚ R] [Fintype n] [DecidableEq n]

omit [Algebra ℚ R] in
@[simp] theorem matrixDerivative_constant (d : Derivation k R R) (J : Matrix n n k) :
    matrixDerivative d ((algebraMap k R).mapMatrix J) = 0 := by
  ext i j
  exact d.map_algebraMap (J i j)

omit [Algebra ℚ R] in
theorem matrixDerivative_smul_constant (d : Derivation k R R) (x : R)
    (J : Matrix n n k) :
    matrixDerivative d (x • (algebraMap k R).mapMatrix J) =
      d x • (algebraMap k R).mapMatrix J := by
  ext i j
  change d (x * algebraMap k R (J i j)) = d x * algebraMap k R (J i j)
  rw [d.leibniz, d.map_algebraMap]
  simp only [smul_eq_mul, mul_zero, zero_add, mul_comm]

/-- Differentiation of each successor-degree exponential term cancels its
factorial denominator exactly. -/
theorem matrixDerivative_exp_term (d : Derivation k R R) (x : R)
    (J : Matrix n n k) (r : ℕ) :
    matrixDerivative d (((r+1).factorial : ℚ)⁻¹ •
      (x • (algebraMap k R).mapMatrix J) ^ (r+1)) =
      d x • ((algebraMap k R).mapMatrix J *
        ((r.factorial : ℚ)⁻¹ • (x • (algebraMap k R).mapMatrix J) ^ r)) := by
  rw [map_rat_smul, smul_pow, ← map_pow, matrixDerivative_smul_constant,
    d.leibniz_pow]
  simp only [Nat.add_one_sub_one, smul_pow, ← map_pow]
  rw [Matrix.mul_smul, Matrix.mul_smul, ← map_mul, ← pow_succ']
  have hc : ((r + 1).factorial : ℚ)⁻¹ * (r + 1 : ℕ) = (r.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have h : (r + 1 : ℚ) ≠ 0 := by positivity
    field_simp
  ext i j
  simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  simp only [smul_assoc]
  rw [← smul_assoc, smul_eq_mul, hc]
  rw [smul_comm (d x) ((r.factorial : ℚ)⁻¹), smul_comm (d x) (x ^ r)]

/-- No invertibility or differential equation for the exponential is assumed.
Nilpotence of the constant matrix is the sole termination hypothesis. -/
theorem matrixDerivative_nilpotent_exp (d : Derivation k R R) (x : R)
    (J : Matrix n n k) (hJ : IsNilpotent J) :
    matrixDerivative d (IsNilpotent.exp (x • (algebraMap k R).mapMatrix J)) =
      d x • ((algebraMap k R).mapMatrix J *
        IsNilpotent.exp (x • (algebraMap k R).mapMatrix J)) := by
  obtain ⟨q, hq⟩ := hJ
  have hp : (x • (algebraMap k R).mapMatrix J) ^ q = 0 := by
    simp only [smul_pow, ← map_pow, hq, map_zero, smul_zero]
  have hs : (x • (algebraMap k R).mapMatrix J) ^ (q+1) = 0 := by
    rw [pow_succ, hp, zero_mul]
  conv_lhs => rw [IsNilpotent.exp_eq_sum hs]
  conv_rhs => rw [IsNilpotent.exp_eq_sum hp]
  rw [Finset.sum_range_succ', map_add, map_sum]
  simp only [pow_zero, matrixDerivative_one, map_rat_smul, smul_zero, add_zero]
  simp only [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simpa only [map_rat_smul] using matrixDerivative_exp_term d x J r

end StrictEUnit
