import NormalizedChartScalarExtension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The two structural premises required by the fixed-W ratio theorem are derived
for every basis of the SAME normalized scalar extension. No determinant or
factorization premise is supplied, and no differential assertion is made.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The coefficient matrix of any basis is its literal pivot-row matrix.
That square matrix has nonzero determinant, derived from basis independence.
All matrix products are genuine matrix multiplication. -/
theorem normalizedChartScalarExtension_basis_factorization
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0)
    (v : Basis (Fin s) L (normalizedChartScalarExtension φ B)) :
    let V : Matrix (Fin r) (Fin s) L :=
      Matrix.of (fun i j => (v j : Fin r → L) i)
    let M : Matrix (Fin s) (Fin s) L := V.submatrix p id
    V = B.map φ * M ∧ M.det ≠ 0 := by
  classical
  let V : Matrix (Fin r) (Fin s) L :=
    Matrix.of (fun i j => (v j : Fin r → L) i)
  let M : Matrix (Fin s) (Fin s) L := V.submatrix p id
  change V = B.map φ * M ∧ M.det ≠ 0
  have hfactor : V = B.map φ * M := by
    apply Matrix.ext
    intro i j
    have h := congrFun (normalizedChartScalarExtension_reconstruct φ B p hB (v j)) i
    change (∑ k : Fin s, (B.map φ) i k * (v j : Fin r → L) (p k)) =
      (v j : Fin r → L) i at h
    change (v j : Fin r → L) i =
      ∑ k : Fin s, (B.map φ) i k * (v j : Fin r → L) (p k)
    exact h.symm
  have hli : LinearIndependent L V.col := by
    have hv := v.linearIndependent.map'
      (normalizedChartScalarExtension φ B).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact hv
  have hinjV : Function.Injective V.mulVec :=
    (Matrix.mulVec_injective_iff (M := V)).mpr hli
  have hinjM : Function.Injective M.mulVec := by
    intro x y hxy
    apply hinjV
    calc
      V *ᵥ x = B.map φ *ᵥ (M *ᵥ x) := by rw [hfactor, ← Matrix.mulVec_mulVec]
      _ = B.map φ *ᵥ (M *ᵥ y) := congrArg (B.map φ).mulVec hxy
      _ = V *ᵥ y := by rw [hfactor, ← Matrix.mulVec_mulVec]
  have hu : IsUnit M := (Matrix.mulVec_injective_iff_isUnit (A := M)).mp hinjM
  exact ⟨hfactor, ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero⟩

end StrictEUnit
end
