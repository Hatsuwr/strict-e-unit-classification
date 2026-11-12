import RationalCovariantRow
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact covariant cyclicity modulo the actual relation kernel. No numerical
rank or ordinary recurrence is assumed to follow from these abstract bridges. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
section Quotient
variable {B M N ι : Type*} [Field B] [AddCommGroup M] [AddCommGroup N]
  [Module B M] [Module B N] [Fintype ι]
theorem linearIndependent_relationQuotient_iff (F : M →ₗ[B] N) (v : ι → M) :
    LinearIndependent B (fun i => (LinearMap.ker F).mkQ (v i)) ↔
      LinearIndependent B (fun i => F (v i)) := by
  have hzero (c : ι → B) :
      (∑ i, c i • (LinearMap.ker F).mkQ (v i) = 0) ↔
        (∑ i, c i • F (v i) = 0) := by
    calc
      _ ↔ (LinearMap.ker F).mkQ (∑ i, c i • v i) = 0 := by simp only [map_sum, map_smul]
      _ ↔ (∑ i, c i • v i) ∈ LinearMap.ker F := Submodule.Quotient.mk_eq_zero _
      _ ↔ _ := by simp only [LinearMap.mem_ker, map_sum, map_smul]
  constructor
  · intro h
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro c hc
    exact h c ((hzero c).2 hc)
  · intro h
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro c hc
    exact h c ((hzero c).1 hc)
end Quotient
section Covariant
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
variable {r : ℕ} (dB : Derivation k B B) (d : Derivation k R R)
  (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (A : Fin r → Fin r → B) (Y : Fin r → R)
  (hY : ∀ i, d (Y i) = ∑ j, A i j • Y j)

include hcompat hY

theorem rationalCovariantRow_preserves_relationKernel (q : Fin r → B)
    (hq : q ∈ LinearMap.ker (Fintype.linearCombination B Y)) :
    rationalCovariantRow dB A q ∈ LinearMap.ker (Fintype.linearCombination B Y) := by
  change (∑ j, rationalCovariantRow dB A q j • Y j) = 0
  change (∑ j, q j • Y j) = 0 at hq
  rw [← rationalCovariantRow_eval dB d hcompat A Y hY, hq, map_zero]

theorem rationalCovariantRow_quotient_independent_iff (q : Fin r → B) (m : ℕ) :
    LinearIndependent B (fun i : Fin m =>
      (LinearMap.ker (Fintype.linearCombination B Y)).mkQ
        (((rationalCovariantRow dB A)^[i.val]) q)) ↔
    LinearIndependent B (fun i : Fin m =>
      ((d : R → R)^[i.val]) (∑ j, q j • Y j)) := by
  rw [linearIndependent_relationQuotient_iff]
  simp only [Fintype.linearCombination_apply,
    ← rationalCovariantRow_iterate_eval dB d hcompat A Y hY q]

theorem rationalCovariantRow_recurrence_iff (q : Fin r → B) (m : ℕ) (b : Fin m → B) :
    (((rationalCovariantRow dB A)^[m]) q -
      ∑ i, b i • ((rationalCovariantRow dB A)^[i.val]) q) ∈
        LinearMap.ker (Fintype.linearCombination B Y) ↔
    (∑ i, b i • ((d : R → R)^[i.val]) (∑ j, q j • Y j)) =
      ((d : R → R)^[m]) (∑ j, q j • Y j) := by
  change (Fintype.linearCombination B Y) _ = 0 ↔ _
  simp only [map_sub, map_sum, map_smul, Fintype.linearCombination_apply]
  simp_rw [← rationalCovariantRow_iterate_eval dB d hcompat A Y hY q]
  rw [sub_eq_zero, eq_comm]

theorem rationalCovariantRow_minimal_prefix_of_quotient (q : Fin r → B) (m : ℕ)
    (hli : LinearIndependent B (fun i : Fin m =>
      (LinearMap.ker (Fintype.linearCombination B Y)).mkQ
        (((rationalCovariantRow dB A)^[i.val]) q)))
    (hnext : (LinearMap.ker (Fintype.linearCombination B Y)).mkQ
        (((rationalCovariantRow dB A)^[m]) q) ∈
      Submodule.span B (Set.range (fun i : Fin m =>
        (LinearMap.ker (Fintype.linearCombination B Y)).mkQ
          (((rationalCovariantRow dB A)^[i.val]) q)))) :
    LinearIndependent B (fun i : Fin m =>
      ((d : R → R)^[i.val]) (∑ j, q j • Y j)) ∧
    ∃! b : Fin m → B, (∑ i, b i • ((d : R → R)^[i.val]) (∑ j, q j • Y j)) =
      ((d : R → R)^[m]) (∑ j, q j • Y j) := by
  classical
  have hli' := (rationalCovariantRow_quotient_independent_iff dB d hcompat A Y hY q m).1 hli
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hnext
  have hz : (LinearMap.ker (Fintype.linearCombination B Y)).mkQ
      (((rationalCovariantRow dB A)^[m]) q -
        ∑ i, b i • ((rationalCovariantRow dB A)^[i.val]) q) = 0 := by
    simpa only [map_sub, map_sum, map_smul, sub_eq_zero] using hb.symm
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hrec := (rationalCovariantRow_recurrence_iff dB d hcompat A Y hY q m b).1 hmem
  refine ⟨hli', b, hrec, ?_⟩
  intro b' hb'
  apply hli'.fintypeLinearCombination_injective
  exact hb'.trans hrec.symm

theorem rationalCovariantRow_minimal_prefix_of_full_quotient_rank
    (q : Fin r → B) (m : ℕ)
    (hdim : m = Module.finrank B ((Fin r → B) ⧸ LinearMap.ker (Fintype.linearCombination B Y)))
    (hli : LinearIndependent B (fun i : Fin m =>
      (LinearMap.ker (Fintype.linearCombination B Y)).mkQ
        (((rationalCovariantRow dB A)^[i.val]) q))) :
    LinearIndependent B (fun i : Fin m =>
      ((d : R → R)^[i.val]) (∑ j, q j • Y j)) ∧
    ∃! b : Fin m → B, (∑ i, b i • ((d : R → R)^[i.val]) (∑ j, q j • Y j)) =
      ((d : R → R)^[m]) (∑ j, q j • Y j) := by
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simpa only [Fintype.card_fin] using hdim)
  apply rationalCovariantRow_minimal_prefix_of_quotient dB d hcompat A Y hY q m hli
  rw [hspan]
  exact Submodule.mem_top
end Covariant
end StrictEUnit
