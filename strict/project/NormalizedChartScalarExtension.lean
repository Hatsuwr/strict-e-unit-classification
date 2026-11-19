import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
Scalar extension of an actual normalized finite coordinate chart.
The extension is defined as the literal range of the mapped column matrix.
Its pivot projection, independent columns, basis and dimension are derived.
No differential or bounded-degree statement occurs here.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The actual L-span of the mapped columns, expressed by their linear-map range. -/
def normalizedChartScalarExtension
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) : Submodule L (Fin r → L) :=
  LinearMap.range (B.map φ).mulVecLin

/-- Literal pivot coordinates recover every coefficient vector after scalar extension. -/
theorem normalizedChart_map_pivot_mulVec
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0)
    (x : Fin s → L) (i : Fin s) :
    ((B.map φ) *ᵥ x) (p i) = x i := by
  classical
  have hm (j : Fin s) : φ (B (p i) j) = if i = j then 1 else 0 := by
    rw [hB]
    by_cases hij : i = j <;> simp [hij]
  change (∑ j : Fin s, (B.map φ) (p i) j * x j) = x i
  simp [hm]

/-- Normalization proves injectivity over L; no linear-independence premise is supplied. -/
theorem normalizedChart_map_mulVec_injective
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0) :
    Function.Injective (B.map φ).mulVec := by
  intro x y h
  funext i
  have hi := congrFun h (p i)
  simpa only [normalizedChart_map_pivot_mulVec φ B p hB] using hi

/-- Every element of the actual extension reconstructs from its own pivot coordinates. -/
theorem normalizedChartScalarExtension_reconstruct
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0)
    (v : normalizedChartScalarExtension φ B) :
    (B.map φ) *ᵥ (fun i => (v : Fin r → L) (p i)) = (v : Fin r → L) := by
  obtain ⟨x, hx⟩ := (LinearMap.mem_range).mp v.property
  have hx' : (B.map φ) *ᵥ x = (v : Fin r → L) := hx
  have hpivot : (fun i => (v : Fin r → L) (p i)) = x := by
    funext i
    rw [← hx']
    exact normalizedChart_map_pivot_mulVec φ B p hB x i
  calc
    (B.map φ) *ᵥ (fun i => (v : Fin r → L) (p i)) = (B.map φ) *ᵥ x :=
      congrArg (B.map φ).mulVec hpivot
    _ = (v : Fin r → L) := hx'

/-- The constructed basis is the mapped original column family, not a replacement family. -/
def mappedNormalizedChartBasis
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0) :
    Basis (Fin s) L (normalizedChartScalarExtension φ B) :=
  (Pi.basisFun L (Fin s)).map
    (LinearEquiv.ofInjective (B.map φ).mulVecLin
      (normalizedChart_map_mulVec_injective φ B p hB))

theorem mappedNormalizedChartBasis_coe
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0)
    (j : Fin s) :
    ((mappedNormalizedChartBasis φ B p hB j : normalizedChartScalarExtension φ B) :
      Fin r → L) = fun i => φ (B i j) := by
  classical
  rw [mappedNormalizedChartBasis, Basis.map_apply]
  funext i
  change ((B.map φ) *ᵥ ((Pi.basisFun L (Fin s)) j)) i = φ (B i j)
  simp only [Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.map_apply]

/-- Range and column-span presentations of the SAME extension agree. -/
theorem normalizedChartScalarExtension_span
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) :
    Submodule.span L (Set.range (fun j : Fin s => fun i : Fin r => φ (B i j))) =
      normalizedChartScalarExtension φ B := by
  exact (Matrix.range_mulVecLin (B.map φ)).symm

/-- The dimension s is derived from the constructed basis, including s=0. -/
theorem normalizedChartScalarExtension_finrank
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0) :
    Module.finrank L (normalizedChartScalarExtension φ B) = s := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (mappedNormalizedChartBasis φ B p hB)

/-- Any finite basis of this same extension has exactly the original chart size. -/
theorem normalizedChartScalarExtension_basis_card
    {F L : Type*} [Field F] [Field L] (φ : F →+* L) {r s t : ℕ}
    (B : Matrix (Fin r) (Fin s) F) (p : Fin s ↪ Fin r)
    (hB : ∀ i j : Fin s, B (p i) j = if i = j then 1 else 0)
    (v : Basis (Fin t) L (normalizedChartScalarExtension φ B)) : t = s := by
  have hv : Module.finrank L (normalizedChartScalarExtension φ B) = t := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis v
  exact hv.symm.trans (normalizedChartScalarExtension_finrank φ B p hB)

end StrictEUnit
end
