import PolynomialConnectionFaceRecurrence
import AttainedIrregularSlope
import ExpandedConnectionIntegrality
import ConstantCompanionArithmeticObstruction

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Exponential common denominators for the SAME connection matrices exclude
an irregular last-row valuation. No alternative scalar operator is selected. -/
theorem companion_common_denominators_local_bounds
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion (n+1) c i j)
    (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ E^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin (n+1), ∀ l : ℕ,
        IsIntegral ℤ ((d:K)*(dividedPolynomialConnectionSequence T U m i j).coeff l)) :
    ∀ j, U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1) := by
  classical
  intro j hj
  by_contra hbad
  let S : Finset (Fin (n+1)) := Finset.univ.filter (fun i => U (Fin.last n) i ≠ 0)
  have hjs : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  have hirr : (U (Fin.last n) j).natTrailingDegree+(n+1-j.val)<T.natTrailingDegree := by
    have hlt := j.isLt
    omega
  obtain ⟨j0,hj0,hh,hha,ha,hcross,heq⟩ := exists_attained_irregular_slope
    (n+1) T.natTrailingDegree (Nat.succ_pos n)
    (fun i => (U (Fin.last n) i).natTrailingDegree) S ⟨j,hjs,hirr⟩
  let h := n+1-j0.val
  let a := T.natTrailingDegree-(U (Fin.last n) j0).natTrailingDegree
  have hV : ∀ i, U (Fin.last n) i ≠ 0 →
      h*T.natTrailingDegree ≤ h*(U (Fin.last n) i).natTrailingDegree+(n+1-i.val)*a := by
    intro i hi
    have hs : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    simpa only [h, a, Nat.mul_comm] using hcross i hs
  let τ := T.coeff T.natTrailingDegree
  let β := polynomialCompanionFace n h a T U
  let u := polynomialConnectionFaceRow n h a T U
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hj0ne : U (Fin.last n) j0 ≠ 0 := (Finset.mem_filter.mp hj0).2
  have hβ : β j0 ≠ 0 := polynomialCompanionFace_ne_zero_of_attained n h a hh T U j0 hj0ne
    (by simpa only [h, a, Nat.mul_comm] using heq)
  have hrec := polynomialConnectionFaceRow_recurrence n c T U hclear h a hh hha ha hV
  have hu : ∀ m, u m = (fun x => x ᵥ* constantCompanion n τ β)^[m] (Pi.single 0 1) := by
    intro m
    induction m with
    | zero => exact hrec.1
    | succ m ih =>
      rw [Function.iterate_succ_apply', ← ih]
      funext i
      have hc := constantCompanion_row_action n τ β (u m)
      cases i using Fin.cases with
      | zero => exact (hrec.2 m).1.trans hc.1.symm
      | succ i => exact ((hrec.2 m).2 i).trans (hc.2 i).symm
  let δ : ℕ → ℕ := fun m => Classical.choose (hden m)
  have hδ (m : ℕ) : 0 < δ m := (Classical.choose_spec (hden m)).1
  have hδbound (m : ℕ) : (δ m:ℝ) ≤ E^(m+1) := (Classical.choose_spec (hden m)).2.1
  have hint (m : ℕ) (i : Fin (n+1)) : IsIntegral ℤ ((δ m:K)*
      (Pi.single 0 1 ᵥ* (constantCompanion n τ β)^m) i / (m.factorial:K)) := by
    rw [← constantCompanion_orbit_eq_power, ← hu m]
    exact polynomialConnectionSequence_expanded_integral T U m (δ m) h hh 0 i
      (irregularPolynomialWeight h T.natTrailingDegree a m i.val)
      ((Classical.choose_spec (hden m)).2.2 m le_rfl 0 i)
  have hzero := constantCompanion_factorial_denominators_force_last_row_zero
    n τ hτ β E hE δ hδ hδbound hint
  exact hβ (hzero j0)

end StrictEUnit
end
