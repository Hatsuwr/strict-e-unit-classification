import ActualRamifiedAmbientScalars
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {C : Type*} {I : C → Type*} {J R S : Type*}
  [Fintype C] [DecidableEq C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
  [Fintype J] [DecidableEq J] [CommRing R] [CommRing S]

theorem mapped_reindexedBlockUnit_row (g : R →+* S)
    (Z : ∀ c, (Matrix (I c) (I c) R)ˣ) (e : (Σ c, I c) ≃ J)
    (f : ∀ c, I c → S) (j : J) :
    (∑ i : J, f (e.symm i).1 (e.symm i).2 * g ((reindexedBlockUnit Z e).val i j)) =
      ∑ i : I (e.symm j).1, f (e.symm j).1 i * g ((Z (e.symm j).1).val i (e.symm j).2) := by
  change (∑ i : J, f (e.symm i).1 (e.symm i).2 *
    g ((finiteBlockUnit Z).val (e.symm i) (e.symm j))) = _
  rw [e.symm.sum_comp (fun i => f i.1 i.2 * g ((finiteBlockUnit Z).val i (e.symm j)))]
  obtain ⟨c,j⟩ := e.symm j
  rw [Fintype.sum_sigma, Finset.sum_eq_single c]
  · simp only [finiteBlockUnit, Matrix.blockDiagonal'_apply_eq]
  · intro b hb hbc
    simp only [finiteBlockUnit, Matrix.blockDiagonal'_apply_ne _ _ _ hbc, map_zero,
      mul_zero, Finset.sum_const_zero]
  · intro hc
    exact (hc (Finset.mem_univ c)).elim

theorem ramified_external_natural_shift {K : Type*} [Field K]
    (N : ℕ) (hN : N ≠ 0) (m s : ℤ) (p : Polynomial (LaurentSeries K)) :
    Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN (frobeniusIntegerShift s p) =
    Polynomial.C (HahnSeries.single (m + (N : ℤ) * s) (1 : K)) *
      stage38_logRamification N hN p := by
  rw [frobeniusIntegerShift, map_mul, stage38_logRamification_monomial,
    ← mul_assoc, ← Polynomial.C_mul, HahnSeries.single_mul_single, one_mul]
end StrictEUnit
end
