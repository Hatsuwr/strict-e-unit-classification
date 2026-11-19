import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Quotient.Basic

/-! New reconstruction from retained proof drafts. Inverse-matrix coordinates
are regular when the lifted completed matrix has unit determinant. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped Matrix BigOperators
namespace StrictEUnit

theorem matrix_regular_row_coordinates
    {F S L ι : Type*}
    [Field F] [CommRing S] [Field L]
    [Fintype ι] [DecidableEq ι]
    (φ : F →+* L) (ψ : S →+* L)
    (H : Matrix ι ι F) (HS : Matrix ι ι S)
    (hmap : HS.map ψ = H.map φ)
    (hunitS : IsUnit HS.det)
    (w : ι → F) (wS : ι → S)
    (hw : ∀ i, ψ (wS i) = φ (w i)) :
    H.det ≠ 0 ∧
      ∃ x : ι → F, ∃ xS : ι → S,
        x ᵥ* H = w ∧
        ∀ i, ψ (xS i) = φ (x i) := by
  have hdmap : ψ HS.det = φ H.det := by
    rw [ψ.map_det, φ.map_det]
    change (HS.map ψ).det = (H.map φ).det
    rw [hmap]
  have huMap : IsUnit (φ H.det) := by
    rw [← hdmap]
    exact hunitS.map ψ
  have hdet : H.det ≠ 0 := by
    intro hz
    exact huMap.ne_zero (by rw [hz, map_zero])
  have huH : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet

  let x : ι → F := w ᵥ* H⁻¹
  let xS : ι → S := wS ᵥ* HS⁻¹

  have hx : x ᵥ* H = w := by
    dsimp only [x]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul H huH,
      Matrix.vecMul_one]

  have hxS : xS ᵥ* HS = wS := by
    dsimp only [xS]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul HS hunitS,
      Matrix.vecMul_one]

  have huL : IsUnit (H.map φ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (φ.mapMatrix H).det
    rw [← φ.map_det]
    exact huH.map φ

  have hi : Function.Injective (H.map φ).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr huL

  have hcoords : ψ ∘ xS = φ ∘ x := by
    apply hi
    calc
      (ψ ∘ xS) ᵥ* H.map φ = ψ ∘ (xS ᵥ* HS) := by
        rw [← hmap]
        funext i
        exact (ψ.map_vecMul HS xS i).symm
      _ = ψ ∘ wS := congrArg (fun u => ψ ∘ u) hxS
      _ = φ ∘ w := funext hw
      _ = (φ ∘ x) ᵥ* H.map φ := by
        rw [← hx]
        funext i
        exact φ.map_vecMul H x i

  exact ⟨hdet, x, xS, hx, fun i => congrFun hcoords i⟩

theorem quotient_independent_of_completed
    {B V I J : Type*}
    [Field B] [AddCommGroup V] [Module B V]
    (N : Submodule B V) (v : I → V) (b : J → V)
    (hN : N = Submodule.span B (Set.range b))
    (hfull : LinearIndependent B (Sum.elim v b)) :
    LinearIndependent B (fun i => N.mkQ (v i)) := by
  have h := linearIndependent_sum.mp hfull
  have hv : LinearIndependent B v := h.1
  change LinearIndependent B (N.mkQ ∘ v)
  apply hv.map
  simpa only [Submodule.ker_mkQ, hN] using h.2.2

end StrictEUnit
