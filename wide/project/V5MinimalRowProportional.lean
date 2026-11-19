import V5AffineMinimumOrder

namespace StrictEUnit
open scoped BigOperators

/-- Evaluate a polynomial-coefficient differential row up to index m. -/
noncomputable def v5RowResidual {K : Type*} [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (m : ℕ) (a : ℕ → Polynomial K) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1),
    (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (a j) * iteratedDeriv j f z

private theorem v5_row_zero_of_no_annihilator_through {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ} (hmin : ∀ n ≤ m, ¬ v5HasAnnihilatorOrder K f n)
    (c : ℕ → Polynomial K) (hc : ∀ z, v5RowResidual f m c z = 0) :
    ∀ j ≤ m, c j = 0 := by
  have htop : c m = 0 := by
    by_contra hne
    exact hmin m le_rfl ⟨c, hne, hc⟩
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa [hj0] using htop
  | succ m ih =>
    have hprev : ∀ z, v5RowResidual f m c z = 0 := by
      intro z
      have h := hc z
      unfold v5RowResidual at h ⊢
      simpa only [Finset.sum_range_succ (f := fun j =>
        (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (c j) * iteratedDeriv j f z) (n := m + 1),
        htop, map_zero, zero_mul, add_zero] using h
    intro j hj
    rcases eq_or_lt_of_le hj with h | h
    · simpa [h] using htop
    · exact ih (fun n hn => hmin n (Nat.le_trans hn (Nat.le_succ m))) hprev
        (by by_contra hne; exact hmin m (Nat.le_succ m) ⟨c, hne, hprev⟩) j
        (Nat.le_of_lt_succ h)

theorem v5_rowResidual_cross {K : Type*} [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (m : ℕ) (a b : ℕ → Polynomial K) (z : ℂ) :
    v5RowResidual f m (fun j => b m * a j - a m * b j) z =
      (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (b m) * v5RowResidual f m a z -
      (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (a m) * v5RowResidual f m b z := by
  unfold v5RowResidual
  simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

/-- Two annihilating rows of the same minimal order are proportional without division. -/
theorem v5_minimal_rows_cross_eq {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ} (hsmall : ∀ n < m, ¬ v5HasAnnihilatorOrder K f n)
    (a b : ℕ → Polynomial K) (ha : ∀ z, v5RowResidual f m a z = 0)
    (hb : ∀ z, v5RowResidual f m b z = 0) :
    ∀ j ≤ m, b m * a j = a m * b j := by
  have hcross : ∀ z, v5RowResidual f m (fun j => b m * a j - a m * b j) z = 0 := by
    intro z
    rw [v5_rowResidual_cross, ha z, hb z, mul_zero, mul_zero, sub_zero]
  intro j hj
  rcases eq_or_lt_of_le hj with h | h
  · rw [h, mul_comm]
  · cases m with
    | zero => exact (Nat.not_lt_zero _ h).elim
    | succ m =>
      have hc : ∀ z, v5RowResidual f m (fun j => b (m + 1) * a j - a (m + 1) * b j) z = 0 := by
        intro z
        have hz := hcross z
        unfold v5RowResidual at hz ⊢
        rw [Finset.sum_range_succ (f := fun j =>
          (Polynomial.eval₂RingHom (algebraMap K ℂ) z)
            (b (m + 1) * a j - a (m + 1) * b j) * iteratedDeriv j f z) (n := m + 1)] at hz
        have hdiag : b (m + 1) * a (m + 1) - a (m + 1) * b (m + 1) = 0 := by ring
        simpa only [hdiag, map_zero, zero_mul, add_zero] using hz
      exact sub_eq_zero.mp
        (v5_row_zero_of_no_annihilator_through
          (fun n hn => hsmall n (Nat.lt_succ_of_le hn)) _ hc j (Nat.le_of_lt_succ h))

/-- The scaled residual identity is valid on every test function, point by point. -/
theorem v5_minimal_rows_scaled_residual {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ} (hsmall : ∀ n < m, ¬ v5HasAnnihilatorOrder K f n)
    (a b : ℕ → Polynomial K) (ha : ∀ z, v5RowResidual f m a z = 0)
    (hb : ∀ z, v5RowResidual f m b z = 0) (u : ℂ → ℂ) (z : ℂ) :
    (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (b m) * v5RowResidual u m a z =
      (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (a m) * v5RowResidual u m b z := by
  apply sub_eq_zero.mp
  rw [← v5_rowResidual_cross]
  unfold v5RowResidual
  apply Finset.sum_eq_zero
  intro j hj
  dsimp only
  rw [v5_minimal_rows_cross_eq hsmall a b ha hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),
    sub_self, map_zero, zero_mul]

/-- Away from both leading-coefficient zero sets, either row vanishes on a test jet
exactly when the other does. This makes no continuity assertion at the excluded points. -/
theorem v5_minimal_rows_residual_zero_iff_of_eval_ne {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ} (hsmall : ∀ n < m, ¬ v5HasAnnihilatorOrder K f n)
    (a b : ℕ → Polynomial K) (ha : ∀ z, v5RowResidual f m a z = 0)
    (hb : ∀ z, v5RowResidual f m b z = 0) (u : ℂ → ℂ) (z : ℂ)
    (haTop : (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (a m) ≠ 0)
    (hbTop : (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (b m) ≠ 0) :
    v5RowResidual u m a z = 0 ↔ v5RowResidual u m b z = 0 := by
  have h := v5_minimal_rows_scaled_residual hsmall a b ha hb u z
  constructor
  · intro hz
    have hzero := h.symm
    rw [hz, mul_zero] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left haTop
  · intro hz
    rw [hz, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hbTop

#print axioms v5_minimal_rows_cross_eq
#print axioms v5_minimal_rows_scaled_residual
#print axioms v5_minimal_rows_residual_zero_iff_of_eval_ne

end StrictEUnit
