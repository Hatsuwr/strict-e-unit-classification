import MatrixDualBinomial
import Mathlib.LinearAlgebra.Basis.Defs

/-!
Differential stability of the scalar-extended range of an actual basis.
No stability after scalar extension, normalized pivot, or field-linearity of
a derivation is assumed. The rectangular column matrix is always Matrix.of.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Rectangular Leibniz, with the row and column dimensions kept separate. -/
theorem coordinateDerivation_rectangular_mulVec
    {k F : Type*} [CommRing k] [Field F] [Algebra k F] {r s : ℕ}
    (d : Derivation k F F) (B : Matrix (Fin r) (Fin s) F) (x : Fin s → F) :
    (fun i => d ((B *ᵥ x) i)) =
      (B.map (fun z => d z)) *ᵥ x + B *ᵥ (fun j => d (x j)) := by
  funext i
  change d (∑ j, B i j*x j) =
    (∑ j, d (B i j)*x j) + ∑ j, B i j*d (x j)
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- The same basis columns generate a stable extended range. Each original
connection column is represented with b.repr; its coefficients are then mapped
through the same differential ring homomorphism. No independent connection
matrix or stable-image premise is supplied. -/
theorem differential_map_basis_range_stable
    {k F L : Type*} [CommRing k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] {r s : ℕ}
    (dF : Derivation k F F) (dL : Derivation k L L) (φ : F →+* L)
    (hφ : ∀ z, dL (φ z) = φ (dF z))
    (A : Matrix (Fin r) (Fin r) F)
    (E : Submodule F (Fin r → F)) (b : Basis (Fin s) F E)
    (hstable : ∀ v : Fin r → F, v ∈ E →
      ((fun i => dF (v i)) - A *ᵥ v) ∈ E) :
    let B : Matrix (Fin r) (Fin s) F := Matrix.of (fun j i => (b i : Fin r → F) j)
    ∀ v : Fin r → L, v ∈ LinearMap.range ((B.map φ).mulVecLin) →
      ((fun i => dL (v i)) - A.map φ *ᵥ v) ∈
        LinearMap.range ((B.map φ).mulVecLin) := by
  classical
  let B : Matrix (Fin r) (Fin s) F := Matrix.of (fun j i => (b i : Fin r → F) j)
  let u : Fin s → E := fun j =>
    ⟨(fun i => dF ((b j : Fin r → F) i)) - A *ᵥ (b j : Fin r → F),
      hstable (b j) (b j).property⟩
  let C : Matrix (Fin s) (Fin s) F := Matrix.of (fun i j => b.repr (u j) i)
  have hentry (i : Fin r) (j : Fin s) :
      (B*C) i j = dF (B i j) - (A*B) i j := by
    have h := congrArg (fun v : E => (v : Fin r → F) i) (b.sum_repr (u j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h
    change (∑ l : Fin s, C l j*B i l) = dF (B i j) - (A*B) i j at h
    calc
      (B*C) i j = ∑ l : Fin s, C l j*B i l := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro l hl
        exact mul_comm _ _
      _ = _ := h
  have hcolumn (i : Fin r) (j : Fin s) :
      dF (B i j) = (A*B) i j + (B*C) i j :=
    (sub_eq_iff_eq_add.mp (hentry i j).symm).trans (add_comm _ _)
  have hmap : (B.map φ).map (fun z => dL z) =
      A.map φ * B.map φ + B.map φ * C.map φ := by
    apply Matrix.ext
    intro i j
    change dL (φ (B i j)) =
      (A.map φ * B.map φ) i j + (B.map φ * C.map φ) i j
    rw [hφ, hcolumn, map_add, RingHom.map_matrix_mul, RingHom.map_matrix_mul]
  change ∀ v : Fin r → L, v ∈ LinearMap.range ((B.map φ).mulVecLin) →
    ((fun i => dL (v i)) - A.map φ *ᵥ v) ∈ LinearMap.range ((B.map φ).mulVecLin)
  intro v hv
  obtain ⟨x, rfl⟩ := (LinearMap.mem_range).mp hv
  have hcalc : (fun i => dL ((B.map φ *ᵥ x) i)) - A.map φ *ᵥ (B.map φ *ᵥ x) =
      B.map φ *ᵥ (C.map φ *ᵥ x + (fun j => dL (x j))) := by
    rw [coordinateDerivation_rectangular_mulVec dL (B.map φ) x, hmap]
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]
    abel
  apply (LinearMap.mem_range).mpr
  exact ⟨C.map φ *ᵥ x + (fun j => dL (x j)), hcalc.symm⟩

end StrictEUnit
end
