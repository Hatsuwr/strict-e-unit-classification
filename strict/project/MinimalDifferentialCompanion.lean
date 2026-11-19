import FirstDerivativeDependence
import Stage14ScalarODEClosure

/-! Source-only generic minimal cyclic differential structure.
Differentiation is k-linear, not B-linear; stability uses the compatible scalar derivation.
The positive-order endpoints require f ≠ 0. The zero case belongs to
FirstDependence.first_dependence_zero_iff and stage14_zero_finiteDifferentialSpan. -/

noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- Shift rows followed by the normalized recurrence row. No derivative is asserted B-linear. -/
def minimalDerivativeCompanion (r : ℕ) (b : Fin r → B) : Fin r → Fin r → B :=
  fun i j => if i.val + 1 < r then (if j.val = i.val + 1 then 1 else 0) else b j

/-- The displayed companion acts on exactly the initial derivatives of the supplied element. -/
theorem minimalDerivativeCompanion_rows (d : Derivation k R R) (f : R)
    (r : ℕ) (b : Fin r → B)
    (hrec : ∑ j, b j • ((d : R → R)^[j.val]) f = ((d : R → R)^[r]) f) :
    ∀ i : Fin r, d (((d : R → R)^[i.val]) f) =
      ∑ j, minimalDerivativeCompanion r b i j • ((d : R → R)^[j.val]) f := by
  classical
  intro i
  rw [← Function.iterate_succ_apply' (d : R → R) i.val f]
  by_cases hi : i.val + 1 < r
  · let t : Fin r := ⟨i.val + 1, hi⟩
    have hsum :
        (∑ j : Fin r, minimalDerivativeCompanion r b i j •
          ((d : R → R)^[j.val]) f) = ((d : R → R)^[t.val]) f := by
      rw [Finset.sum_eq_single t]
      · simp [minimalDerivativeCompanion, hi, t]
      · intro j _ hj
        have hjval : j.val ≠ i.val + 1 := by
          intro heq
          apply hj
          exact Fin.ext heq
        simp [minimalDerivativeCompanion, hi, hjval]
      · intro ht
        exact (ht (Finset.mem_univ t)).elim
    exact hsum.symm
  · have hn : i.val + 1 = r :=
      Nat.le_antisymm (Nat.succ_le_of_lt i.isLt) (Nat.le_of_not_gt hi)
    simpa only [minimalDerivativeCompanion, Nat.succ_eq_add_one, hn,
      if_neg (Nat.lt_irrefl r)] using hrec.symm

/-- Finite dependence yields a positive independent initial span, unique normalized
recurrence, and actual differential stability. No stability/minimality premise is supplied. -/
theorem exists_minimal_stable_derivative_span
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (f : R) (hf : f ≠ 0) (m : ℕ) (c : Fin (m + 1) → B)
    (hc : ∃ i, c i ≠ 0)
    (hrel : ∑ i, c i • ((d : R → R)^[i.val]) f = 0) :
    ∃ r, 0 < r ∧ r ≤ m ∧
      LinearIndependent B (fun i : Fin r => ((d : R → R)^[i.val]) f) ∧
      (∃! b : Fin r → B, ∑ i, b i • ((d : R → R)^[i.val]) f =
        ((d : R → R)^[r]) f) ∧
      (∀ x ∈ stage14_initialDerivativeSpan (B := B) d f r,
        d x ∈ stage14_initialDerivativeSpan (B := B) d f r) := by
  obtain ⟨r, hpos, hr, hli, hnext, hcoords⟩ :=
    FirstDependence.exists_positive_first_dependence
      (fun n => ((d : R → R)^[n]) f) hf m c hc hrel
  exact ⟨r, hpos, hr, hli, hcoords,
    stage14_initialDerivativeSpan_stable dB d hcompat f r hnext⟩

/-- Construct the exact minimal companion system from the original finite relation.
The coefficients, independence, recurrence and stable span are all derived together. -/
theorem exists_minimal_derivative_companion
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (f : R) (hf : f ≠ 0) (m : ℕ) (c : Fin (m + 1) → B)
    (hc : ∃ i, c i ≠ 0)
    (hrel : ∑ i, c i • ((d : R → R)^[i.val]) f = 0) :
    ∃ r, 0 < r ∧ r ≤ m ∧ ∃ b : Fin r → B,
      LinearIndependent B (fun i : Fin r => ((d : R → R)^[i.val]) f) ∧
      (∑ i, b i • ((d : R → R)^[i.val]) f = ((d : R → R)^[r]) f) ∧
      (∀ b' : Fin r → B,
        (∑ i, b' i • ((d : R → R)^[i.val]) f = ((d : R → R)^[r]) f) → b' = b) ∧
      (∀ x ∈ stage14_initialDerivativeSpan (B := B) d f r,
        d x ∈ stage14_initialDerivativeSpan (B := B) d f r) ∧
      (∀ i : Fin r, d (((d : R → R)^[i.val]) f) =
        ∑ j, minimalDerivativeCompanion r b i j • ((d : R → R)^[j.val]) f) := by
  obtain ⟨r, hpos, hr, hli, hcoords, hstable⟩ :=
    exists_minimal_stable_derivative_span dB d hcompat f hf m c hc hrel
  obtain ⟨b, hb, huniq⟩ := hcoords
  exact ⟨r, hpos, hr, b, hli, hb, huniq, hstable,
    minimalDerivativeCompanion_rows d f r b hb⟩

end StrictEUnit
