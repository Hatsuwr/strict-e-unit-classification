import RamifiedBaseDifferential

/-! The constructed base matrix satisfies the manuscript's exact normalized
ODE, not just its N-fold Laurent Euler rescaling. -/
noncomputable section
namespace StrictEUnit

section ScalarDerivation
variable {k R n : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Entrywise differentiation respects scalar rescaling of the derivation. -/
theorem matrixDerivative_smul_derivation (d : Derivation k R R) (c : k)
    (A : Matrix n n R) : matrixDerivative (c • d) A = c • matrixDerivative d A := by
  apply Matrix.ext
  intro i j
  rfl
end ScalarDerivation

variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

omit [CharZero k] [Fintype n] in
/-- The inverse ramification factor produces the rational exponent m_i/N. -/
theorem ramifiedWeightMatrix_inv_smul (N : ℕ) (m : n → ℤ) :
    (N:k)⁻¹ • ramifiedWeightMatrix (k := k) m =
      Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) ((m i:k) / (N:k))) := by
  apply Matrix.ext
  intro i j
  change ((N:k)⁻¹ • Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) (m i:k))) i j = _
  rw [← Matrix.diagonal_smul]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    change (N:k)⁻¹ • algebraMap k (LaurentLogBase k) (m i:k) = _
    rw [Algebra.smul_def, ← map_mul, div_eq_mul_inv, mul_comm]
  · simp only [Matrix.diagonal_apply_ne _ hij]

/-- With the exact derivation used by the manuscript's candidate APIs,
D_N(t)=t/N and D_N(ell)=1, the constructed matrix satisfies
D_N(Z)=(diag(m_i/N)+J_B)Z. No scaling is left implicit. -/
theorem ramifiedBaseMatrix_manuscript_derivative (N : ℕ) (hN : N ≠ 0)
    (m : n → ℤ) (J : Matrix n n k) (hJ : IsNilpotent J)
    (hweight : RespectsRamifiedWeights m J) :
    matrixDerivative (manuscriptBaseDerivation (k := k) N)
      (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) =
      (Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) ((m i:k) / (N:k))) +
        ramifiedConstantMatrix J) *
      (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) := by
  have hNk : (N:k) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h := congrArg (fun A : Matrix n n (LaurentLogBase k) => (N:k)⁻¹ • A)
    (ramifiedBaseMatrix_derivative N hN m J hJ hweight)
  simp only [ramifiedBaseDerivation, matrixDerivative_smul_derivation, smul_smul,
    inv_mul_cancel₀ hNk, one_smul] at h
  rw [← Matrix.smul_mul, smul_add, smul_smul, inv_mul_cancel₀ hNk, one_smul,
    ramifiedWeightMatrix_inv_smul] at h
  exact h

end StrictEUnit
