import RationalCovariantRow
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Source-only semilinear row stabilization and a scalar annihilator of the same
nonzero remainder. No quantitative zero estimate or full-rank claim is included. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- Covariant differentiation is additive, not B-linear. -/
theorem rationalCovariantRow_add {r : ℕ} (dB : Derivation k B B)
    (A : Fin r → Fin r → B) (q p : Fin r → B) :
    rationalCovariantRow dB A (q + p) =
      rationalCovariantRow dB A q + rationalCovariantRow dB A p := by
  funext j
  simp only [rationalCovariantRow, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ac_rfl

/-- The exact scalar Leibniz term is retained. -/
theorem rationalCovariantRow_smul {r : ℕ} (dB : Derivation k B B)
    (A : Fin r → Fin r → B) (b : B) (q : Fin r → B) :
    rationalCovariantRow dB A (b • q) =
      dB b • q + b • rationalCovariantRow dB A q := by
  funext j
  simp only [rationalCovariantRow, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    dB.leibniz, mul_add, Finset.mul_sum, mul_assoc]
  ac_rfl

/-- Finite sums obey the same additive operator. -/
theorem rationalCovariantRow_sum {r : ℕ} (dB : Derivation k B B)
    (A : Fin r → Fin r → B) {ι : Type*} (s : Finset ι) (q : ι → Fin r → B) :
    rationalCovariantRow dB A (∑ i ∈ s, q i) =
      ∑ i ∈ s, rationalCovariantRow dB A (q i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      funext j
      simp [rationalCovariantRow]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rationalCovariantRow_add, ih]

/-- Row dimension r supplies a nontrivial relation among the first r+1 iterates. -/
theorem rationalCovariantRow_finite_relation {r : ℕ} (dB : Derivation k B B)
    (A : Fin r → Fin r → B) (q : Fin r → B) :
    ∃ c : Fin (r + 1) → B, (∃ i, c i ≠ 0) ∧
      ∑ i, c i • ((rationalCovariantRow dB A)^[i.val]) q = 0 := by
  have hdep : ¬ LinearIndependent B
      (fun i : Fin (r + 1) => ((rationalCovariantRow dB A)^[i.val]) q) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hcard
    exact Nat.not_succ_le_self r hcard
  obtain ⟨c, hrel, hc⟩ := Fintype.not_linearIndependent_iff.mp hdep
  exact ⟨c, hc, hrel⟩

/-- The first row dependence makes its initial span stable by the scalar Leibniz rule. -/
theorem rationalCovariantRow_initial_span_stable {r : ℕ}
    (dB : Derivation k B B) (A : Fin r → Fin r → B) (q : Fin r → B) (s : ℕ)
    (hnext : ((rationalCovariantRow dB A)^[s]) q ∈
      Submodule.span B (Set.range (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q))) :
    ∀ x ∈ Submodule.span B (Set.range
      (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q)),
      rationalCovariantRow dB A x ∈ Submodule.span B (Set.range
        (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q)) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      change rationalCovariantRow dB A
        (((rationalCovariantRow dB A)^[i.val]) q) ∈ _
      rw [← Function.iterate_succ_apply' (rationalCovariantRow dB A) i.val q]
      by_cases hi : i.val + 1 < s
      · exact Submodule.subset_span ⟨⟨i.val + 1, hi⟩, rfl⟩
      · have heq : i.val.succ = s :=
          Nat.le_antisymm (Nat.succ_le_of_lt i.isLt) (Nat.le_of_not_gt hi)
        simpa only [heq] using hnext
  | zero =>
      have hz : rationalCovariantRow dB A (0 : Fin r → B) = 0 := by
        funext j
        simp [rationalCovariantRow]
      rw [hz]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [rationalCovariantRow_add]
      exact Submodule.add_mem _ ihx ihy
  | smul b x hx ih =>
      rw [rationalCovariantRow_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ ih)

/-- Stability identifies the prefix span with the span of ALL covariant iterates. -/
theorem rationalCovariantRow_span_eq_initial {r : ℕ}
    (dB : Derivation k B B) (A : Fin r → Fin r → B) (q : Fin r → B)
    (s : ℕ) (hs : 0 < s)
    (hnext : ((rationalCovariantRow dB A)^[s]) q ∈
      Submodule.span B (Set.range (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q))) :
    Submodule.span B (Set.range (fun n : ℕ => ((rationalCovariantRow dB A)^[n]) q)) =
      Submodule.span B (Set.range (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q)) := by
  have hstable := rationalCovariantRow_initial_span_stable dB A q s hnext
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    induction n with
    | zero => exact Submodule.subset_span ⟨⟨0, hs⟩, rfl⟩
    | succ n ih =>
        simpa only [Function.iterate_succ_apply'] using hstable _ ih
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.val, rfl⟩

/-- Construct positive order s≤r, a stable independent row prefix, unique row
recurrence and its normalized scalar annihilator of precisely the same remainder. -/
theorem exists_covariant_remainder_annihilator {r : ℕ}
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (A : Fin r → Fin r → B) (Y : Fin r → R)
    (hY : ∀ i, d (Y i) = ∑ j, A i j • Y j) (q : Fin r → B)
    (hrem : (∑ j, q j • Y j) ≠ 0) :
    ∃ s, 0 < s ∧ s ≤ r ∧
      Module.finrank B (Submodule.span B
        (Set.range (fun n : ℕ => ((rationalCovariantRow dB A)^[n]) q))) = s ∧
      (Submodule.span B (Set.range (fun n : ℕ => ((rationalCovariantRow dB A)^[n]) q)) =
        Submodule.span B (Set.range
          (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q))) ∧
      LinearIndependent B (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q) ∧
      (∀ x ∈ Submodule.span B (Set.range
        (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q)),
        rationalCovariantRow dB A x ∈ Submodule.span B (Set.range
          (fun i : Fin s => ((rationalCovariantRow dB A)^[i.val]) q))) ∧
      ∃ b : Fin s → B,
        (∑ i, b i • ((rationalCovariantRow dB A)^[i.val]) q =
          ((rationalCovariantRow dB A)^[s]) q) ∧
        (∀ b' : Fin s → B,
          (∑ i, b' i • ((rationalCovariantRow dB A)^[i.val]) q =
            ((rationalCovariantRow dB A)^[s]) q) → b' = b) ∧
        ((d : R → R)^[s]) (∑ j, q j • Y j) =
          ∑ i, b i • ((d : R → R)^[i.val]) (∑ j, q j • Y j) := by
  have hq : q ≠ 0 := by
    intro hz
    apply hrem
    simp [hz]
  obtain ⟨c, hc, hrel⟩ := rationalCovariantRow_finite_relation dB A q
  obtain ⟨s, hpos, hs, hli, hnext, b, hb, huniq⟩ :=
    FirstDependence.exists_positive_first_dependence
      (fun n => ((rationalCovariantRow dB A)^[n]) q) hq r c hc hrel
  have hspan := rationalCovariantRow_span_eq_initial dB A q s hpos hnext
  have hdim : Module.finrank B (Submodule.span B
      (Set.range (fun n : ℕ => ((rationalCovariantRow dB A)^[n]) q))) = s := by
    rw [hspan]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  refine ⟨s, hpos, hs, hdim, hspan, hli,
    rationalCovariantRow_initial_span_stable dB A q s hnext, b, hb, huniq, ?_⟩
  have heval := congrArg (Fintype.linearCombination B Y) hb
  rw [map_sum] at heval
  simp only [map_smul, Fintype.linearCombination_apply] at heval
  simp_rw [← rationalCovariantRow_iterate_eval dB d hcompat A Y hY q] at heval
  exact heval.symm

end StrictEUnit
end
