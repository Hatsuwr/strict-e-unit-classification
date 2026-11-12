import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
A proper normalized rational coordinate chart has an actual nonzero polynomial
annihilator. Only one nonpivot row is cleared, using at most s denominators.
The degree bound is s*D; the empty chart uses the empty product 1.
No differential stability or uniform system-degree bound is assumed or claimed.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- A finite product of s polynomials of degree at most D has degree at most s*D. -/
theorem polynomial_fin_product_degree_bound
    {K : Type*} [CommSemiring K] {s D : ℕ}
    (f : Fin s → Polynomial K) (hf : ∀ j, (f j).natDegree ≤ D) :
    (∏ j, f j).natDegree ≤ s * D := by
  calc
    (∏ j, f j).natDegree ≤ ∑ j, (f j).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ f
    _ ≤ ∑ _j : Fin s, D := Finset.sum_le_sum (fun j _ => hf j)
    _ = s * D := by simp

/-- The row is explicitly constructed by clearing one nonpivot chart row.
Its nonzero coordinate and its action on the entire literal range are derived. -/
theorem exists_polynomial_annihilator_of_normalized_chart
    {K : Type*} [Field K] {r s D : ℕ} (hsr : s < r)
    (B : Matrix (Fin r) (Fin s) (RatFunc K)) (p : Fin s ↪ Fin r)
    (hB : ∀ j k : Fin s, B (p j) k = if j = k then 1 else 0)
    (hdegree : ∀ i : Fin r, ∀ j : Fin s,
      ∃ num den : Polynomial K, den ≠ 0 ∧
        num.natDegree ≤ D ∧ den.natDegree ≤ D ∧
        B i j = algebraMap (Polynomial K) (RatFunc K) num /
          algebraMap (Polynomial K) (RatFunc K) den) :
    ∃ a : Fin r → Polynomial K, (∃ i, a i ≠ 0) ∧
      (∀ i, (a i).natDegree ≤ s * D) ∧
      ∀ v ∈ LinearMap.range B.mulVecLin,
        ∑ i, algebraMap (Polynomial K) (RatFunc K) (a i) * v i = 0 := by
  classical
  have hnot : ¬Function.Surjective p := by
    intro hsurj
    have hle : r ≤ s := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective p hsurj
    exact (Nat.not_le_of_gt hsr) hle
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hpi (j : Fin s) : i ≠ p j := fun h => hi ⟨j, h.symm⟩
  choose num den hden hnumdeg hdendeg hfrac using hdegree i
  let φ : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  let Q : Polynomial K := ∏ j, den j
  let R : Fin s → Polynomial K := fun j => ∏ k, Function.update den j (num j) k
  have hQne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hden j)
  have hQdeg : Q.natDegree ≤ s * D :=
    polynomial_fin_product_degree_bound den hdendeg
  have hRdeg (j : Fin s) : (R j).natDegree ≤ s * D := by
    apply polynomial_fin_product_degree_bound
    intro k
    by_cases hkj : k = j
    · subst k
      simpa only [Function.update_self] using hnumdeg j
    · simpa only [Function.update_of_ne hkj] using hdendeg k
  have hclear (j : Fin s) : φ Q * B i j = φ (R j) := by
    have hQj : Q = den j * ∏ k ∈ Finset.univ \ {j}, den k :=
      Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ j) den
    have hRj : R j = num j * ∏ k ∈ Finset.univ \ {j}, den k :=
      Finset.prod_update_of_mem (Finset.mem_univ j) den (num j)
    have hdj : φ (den j) ≠ 0 := RatFunc.algebraMap_ne_zero (hden j)
    rw [hQj, hRj, map_mul, map_mul, hfrac j]
    change (φ (den j) * φ (∏ k ∈ Finset.univ \ {j}, den k)) *
      (φ (num j) / φ (den j)) =
      φ (num j) * φ (∏ k ∈ Finset.univ \ {j}, den k)
    field_simp [hdj] <;> ring
  let a : Fin r → Polynomial K := fun k =>
    (if k = i then Q else 0) - ∑ j : Fin s, if k = p j then R j else 0
  have hai : a i = Q := by simp [a, hpi]
  have hane : a i ≠ 0 := fun hz => hQne (hai.symm.trans hz)
  have hadeg (k : Fin r) : (a k).natDegree ≤ s * D := by
    change ((if k = i then Q else 0) -
      ∑ j : Fin s, if k = p j then R j else 0).natDegree ≤ s * D
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · by_cases hki : k = i
      · simpa only [if_pos hki] using hQdeg
      · simp only [if_neg hki, Polynomial.natDegree_zero, Nat.zero_le]
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      by_cases hkj : k = p j
      · simpa only [if_pos hkj] using hRdeg j
      · simp only [if_neg hkj, Polynomial.natDegree_zero, Nat.zero_le]
  have hamap (k : Fin r) : φ (a k) =
      (if k = i then φ Q else 0) -
        ∑ j : Fin s, if k = p j then φ (R j) else 0 := by
    simp only [a, map_sub, map_sum, apply_ite φ, map_zero]
  have hcolumn (j : Fin s) : ∑ k : Fin r, φ (a k) * B k j = 0 := by
    calc
      (∑ k : Fin r, φ (a k) * B k j) =
          (∑ k : Fin r, (if k = i then φ Q else 0) * B k j) -
          ∑ k : Fin r, ∑ l : Fin s,
            (if k = p l then φ (R l) else 0) * B k j := by
        simp only [hamap, sub_mul, Finset.sum_mul, Finset.sum_sub_distrib]
      _ = φ Q * B i j - ∑ l : Fin s, φ (R l) * B (p l) j := by
        rw [Finset.sum_comm]
        simp [ite_mul]
      _ = φ Q * B i j - φ (R j) := by simp [hB, mul_ite]
      _ = 0 := sub_eq_zero.mpr (hclear j)
  have hvec : (fun k => φ (a k)) ᵥ* B = 0 := by
    funext j
    exact hcolumn j
  refine ⟨a, ⟨i, hane⟩, hadeg, ?_⟩
  intro v hv
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hv
  change B *ᵥ x = v at hx
  rw [← hx]
  change (fun k => φ (a k)) ⬝ᵥ (B *ᵥ x) = 0
  rw [Matrix.dotProduct_mulVec, hvec, zero_dotProduct]

/-- The identical row annihilates the actual column span, with no chosen
linear-combination coefficients or nonzero-annihilator premise. -/
theorem exists_polynomial_annihilator_of_normalized_chart_span
    {K : Type*} [Field K] {r s D : ℕ} (hsr : s < r)
    (B : Matrix (Fin r) (Fin s) (RatFunc K)) (p : Fin s ↪ Fin r)
    (hB : ∀ j k : Fin s, B (p j) k = if j = k then 1 else 0)
    (hdegree : ∀ i : Fin r, ∀ j : Fin s,
      ∃ num den : Polynomial K, den ≠ 0 ∧
        num.natDegree ≤ D ∧ den.natDegree ≤ D ∧
        B i j = algebraMap (Polynomial K) (RatFunc K) num /
          algebraMap (Polynomial K) (RatFunc K) den) :
    ∃ a : Fin r → Polynomial K, (∃ i, a i ≠ 0) ∧
      (∀ i, (a i).natDegree ≤ s * D) ∧
      ∀ v ∈ Submodule.span (RatFunc K) (Set.range (fun j => fun i => B i j)),
        ∑ i, algebraMap (Polynomial K) (RatFunc K) (a i) * v i = 0 := by
  obtain ⟨a, ha, hdeg, hann⟩ :=
    exists_polynomial_annihilator_of_normalized_chart hsr B p hB hdegree
  refine ⟨a, ha, hdeg, ?_⟩
  intro v hv
  apply hann v
  rw [Matrix.range_mulVecLin]
  exact hv

end StrictEUnit
end
