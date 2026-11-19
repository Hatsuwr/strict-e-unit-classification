import ConstantCompanionObstruction
import FactorialDenominatorObstruction

noncomputable section
open scoped BigOperators Matrix
open Filter
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A fixed finite matrix has an exponential House bound for its original
first-basis row orbit; no per-order growth assumption is supplied. -/
theorem matrix_first_row_orbit_house_bound (n : ℕ)
    (C : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ m j,
      NumberField.house (((fun x => x ᵥ* C)^[m] (Pi.single 0 1)) j) ≤ B^(m+1) := by
  classical
  let B : ℝ := 1 + ∑ j, ∑ i, NumberField.house (C i j)
  have hcol0 (j : Fin (n+1)) : 0 ≤ ∑ i, NumberField.house (C i j) :=
    Finset.sum_nonneg (fun i _ => NumberField.house_nonneg _)
  have hB : 1 ≤ B := by
    have h : 0 ≤ ∑ j : Fin (n+1), ∑ i, NumberField.house (C i j) :=
      Finset.sum_nonneg (fun j _ => hcol0 j)
    dsimp [B]; linarith
  have hcol (j : Fin (n+1)) : (∑ i, NumberField.house (C i j)) ≤ B := by
    have h := Finset.single_le_sum (f:=fun j : Fin (n+1) => ∑ i, NumberField.house (C i j))
      (fun j _ => hcol0 j) (Finset.mem_univ j)
    change (∑ i, NumberField.house (C i j)) ≤
      ∑ j : Fin (n+1), ∑ i, NumberField.house (C i j) at h
    dsimp [B]; linarith
  refine ⟨B,hB,?_⟩
  intro m
  induction m with
  | zero =>
    intro j
    have hz : NumberField.house (0:K) = 0 := by
      simpa using (NumberField.house_intCast (K:=K) 0)
    have ho : NumberField.house (1:K) = 1 := by
      simpa using (NumberField.house_intCast (K:=K) 1)
    simp only [Function.iterate_zero, id_eq, Nat.zero_add, pow_one, Pi.single_apply]
    split_ifs <;> simp only [hz,ho] <;> linarith
  | succ m ih =>
    intro j
    rw [Function.iterate_succ_apply']
    change NumberField.house (∑ i, ((fun x => x ᵥ* C)^[m] (Pi.single 0 1)) i * C i j) ≤ _
    calc
      _ ≤ ∑ i, NumberField.house
          (((fun x => x ᵥ* C)^[m] (Pi.single 0 1)) i * C i j) :=
        NumberField.house_sum_le_sum_house Finset.univ _
      _ ≤ ∑ i, B^(m+1) * NumberField.house (C i j) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (NumberField.house_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (ih i) (NumberField.house_nonneg _))
      _ = B^(m+1) * ∑ i, NumberField.house (C i j) := (Finset.mul_sum ..).symm
      _ ≤ B^(m+1)*B := mul_le_mul_of_nonneg_left (hcol j) (pow_nonneg (zero_le_one.trans hB) _)
      _ = B^(m+1+1) := (pow_succ _ _).symm

/-- Exponential positive integer clearing of every factorially divided orbit
entry forces the companion's last row to vanish. The integer sequence is
shared by all columns and is unchanged. -/
theorem constantCompanion_factorial_denominators_force_last_row_zero
    (n : ℕ) (t : K) (ht : t ≠ 0) (v : Fin (n+1) → K)
    (D : ℝ) (hD : 1 ≤ D) (δ : ℕ → ℕ)
    (hδ : ∀ m, 0 < δ m) (hbound : ∀ m, (δ m:ℝ) ≤ D^(m+1))
    (hint : ∀ m j, IsIntegral ℤ ((δ m:K) *
      (Pi.single 0 1 ᵥ* (constantCompanion n t v)^m) j / (m.factorial:K))) :
    ∀ j, v j = 0 := by
  classical
  obtain ⟨B,hB,hhouse⟩ := matrix_first_row_orbit_house_bound n (constantCompanion n t v)
  have hz : ∀ j : Fin (n+1), ∀ᶠ m : ℕ in atTop,
      (Pi.single 0 1 ᵥ* (constantCompanion n t v)^m) j = 0 := by
    intro j
    apply factorial_denominator_eventually_eq_zero B D hB hD
      (fun m => (Pi.single 0 1 ᵥ* (constantCompanion n t v)^m) j) δ hδ hbound
    · intro m
      simpa only [constantCompanion_orbit_eq_power] using hhouse m j
    · intro m; exact hint m j
  have hall := Filter.eventually_all.mpr hz
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hall
  intro j
  by_contra hj
  apply constantCompanion_power_not_eventually_zero n t ht v ⟨j,hj⟩
  refine ⟨N,fun m hm => ?_⟩
  funext i
  exact hN m hm i

end StrictEUnit
end
