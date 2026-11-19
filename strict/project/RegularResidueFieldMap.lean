import RegularResidueIndicialRoots

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

theorem regularCompanionResidue_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (n : ℕ) (τ : K) (β : Fin (n+1) → K) :
    (regularCompanionResidue n τ β).map φ=
      regularCompanionResidue n (φ τ) (fun j => φ (β j)) := by
  classical
  ext i j
  cases i using Fin.lastCases with
  | last =>
    by_cases hj : Fin.last n=j
    · subst j
      simp [regularCompanionResidue,constantCompanion,Matrix.diagonal_apply]
    · simp [regularCompanionResidue,constantCompanion,Matrix.diagonal_apply,hj]
  | cast i =>
    by_cases hj : i.castSucc=j
    · subst j
      simp [regularCompanionResidue,constantCompanion,Matrix.diagonal_apply,Pi.single_apply]
    · simp [regularCompanionResidue,constantCompanion,Matrix.diagonal_apply,Pi.single_apply,hj]

theorem matrixFallingProduct_map {K L : Type*} [Field K] [Field L]
    {r : ℕ} (φ : K →+* L) (M : Matrix (Fin r) (Fin r) K) :
    ∀ m,(matrixFallingProduct M m).map φ=matrixFallingProduct (M.map φ) m := by
  classical
  intro m
  induction m with
  | zero =>
    ext i j
    simp [matrixFallingProduct,Matrix.one_apply]
  | succ m ih =>
    have hstep : (M-(m:K) • 1).map φ=M.map φ-(m:L) • 1 := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
    change (matrixFallingProduct M m*(M-(m:K) • 1)).map φ=_
    calc
      _ = (matrixFallingProduct M m).map φ*(M-(m:K) • 1).map φ := by
        ext i j
        exact RingHom.map_matrix_mul _ _ i j φ
      _ = _ := by rw [ih,hstep,matrixFallingProduct]

/-- Exact transport of the SAME normalized residue binomial rows; factorial
and scalar inverses are mapped through actual field homomorphisms. -/
theorem regularResidueBinomialRow_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (n : ℕ) (τ : K) (β : Fin (n+1) → K) (m : ℕ) (j : Fin (n+1)) :
    φ (regularResidueBinomialRow n τ β m j)=
      regularResidueBinomialRow n (φ τ) (fun j => φ (β j)) m j := by
  classical
  have hp := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) L => M 0 j)
    (matrixFallingProduct_map φ (regularCompanionResidue n τ β) m)
  rw [regularCompanionResidue_map] at hp
  simp only [Matrix.map_apply] at hp
  simp only [regularResidueBinomialRow,Matrix.single_vecMul,one_smul,
    Pi.smul_apply,smul_eq_mul,map_mul,map_inv₀,map_natCast]
  rw [hp]

end StrictEUnit
end
