import V5PolynomialRowComposition

namespace StrictEUnit
open scoped BigOperators Topology

/-- A triangular table with fixed diagonal admits elimination without
division: a power of the diagonal times the input is a row combination of the
table, plus a remainder strictly below the first diagonal index. -/
theorem v5_triangular_polynomial_pseudoDivide {K : Type*} [Field K]
    (m r : ℕ) (c : Polynomial K) (T : ℕ → ℕ → Polynomial K)
    (htop : ∀ j, T j (m+j) = c)
    (hside : ∀ j k, m+j < k → T j k = 0)
    (p : ℕ → Polynomial K) (hp : ∀ k, m+r < k → p k = 0) :
    ∃ b R : ℕ → Polynomial K,
      (∀ k, r < k → b k = 0) ∧
      (∀ k, m ≤ k → R k = 0) ∧
      ∀ k, c^(r+1) * p k = (∑ j ∈ Finset.range (r+1), b j * T j k) + R k := by
  induction r generalizing p with
  | zero =>
    let b : ℕ → Polynomial K := fun j => if j = 0 then p m else 0
    let R : ℕ → Polynomial K := fun k => c * p k - p m * T 0 k
    refine ⟨b, R, fun k hk => if_neg (by omega), ?_, ?_⟩
    · intro k hk
      rcases eq_or_lt_of_le hk with h | h
      · subst k
        have ht : T 0 m = c := by simpa using htop 0
        simp [R, ht, mul_comm c]
      · have h' : m+0 < k := by omega
        simp [R, hp k h', hside 0 k h']
    · intro k
      simp [b, R]
  | succ r ih =>
    let q : ℕ → Polynomial K := fun k => c * p k - p (m+(r+1)) * T (r+1) k
    have hq : ∀ k, m+r < k → q k = 0 := by
      intro k hk
      have hk' : m+(r+1) ≤ k := by omega
      rcases eq_or_lt_of_le hk' with h | h
      · subst k
        simp [q, htop (r+1), mul_comm c]
      · simp [q, hp k h, hside (r+1) k h]
    obtain ⟨b, R, hb, hR, hEq⟩ := ih q hq
    let B : ℕ → Polynomial K := fun j =>
      if j = r+1 then c^(r+1) * p (m+(r+1)) else b j
    refine ⟨B, R, ?_, hR, ?_⟩
    · intro k hk
      exact (if_neg (by omega)).trans (hb k (by omega))
    · intro k
      have hsum : (∑ j ∈ Finset.range (r+1), B j * T j k) =
          ∑ j ∈ Finset.range (r+1), b j * T j k := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simp [B, show j ≠ r+1 by omega]
      rw [Finset.sum_range_succ, hsum]
      simp only [B, if_pos rfl]
      calc
        _ = c^(r+1) * q k + c^(r+1) * p (m+(r+1)) * T (r+1) k := by
          simp only [q, pow_succ c (r+1)]
          ring
        _ = _ := by rw [hEq]; ac_rfl

/-- The quotient's leading coefficient is forced by the top equation. -/
theorem v5_triangular_pseudoDivide_top {K : Type*} [Field K]
    (m r : ℕ) (c : Polynomial K) (hc : c ≠ 0) (T : ℕ → ℕ → Polynomial K)
    (htop : ∀ j, T j (m+j) = c)
    (hside : ∀ j k, m+j < k → T j k = 0)
    (p b R : ℕ → Polynomial K)
    (hR : ∀ k, m ≤ k → R k = 0)
    (hEq : ∀ k, c^(r+1) * p k = (∑ j ∈ Finset.range (r+1), b j * T j k) + R k) :
    b r = c^r * p (m+r) := by
  have h := hEq (m+r)
  rw [Finset.sum_range_succ, htop, hR _ (by omega), add_zero] at h
  have hz : (∑ j ∈ Finset.range r, b j * T j (m+r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [hside j _ (by omega), mul_zero]
  rw [hz, zero_add] at h
  apply mul_right_cancel₀ hc
  rw [← h, pow_succ]
  ring

/-- A lower-cutoff annihilating polynomial row has all coefficients zero
when the original scalar function has strictly larger minimal order. -/
theorem v5_remainder_eq_zero_of_minimal {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ}
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder K f l)
    {n : ℕ} (hn : n < m) (p : ℕ → Polynomial K)
    (hp : ∀ z, v5RowResidual f n p z = 0) :
    ∀ k ≤ n, p k = 0 := by
  induction n with
  | zero =>
    have hp0 : p 0 = 0 := by
      by_contra h
      exact hmin 0 hn ⟨p, h, hp⟩
    intro k hk
    simpa [show k = 0 by omega] using hp0
  | succ n ih =>
    have htop : p (n+1) = 0 := by
      by_contra h
      exact hmin (n+1) hn ⟨p, h, hp⟩
    have hsmall : ∀ z, v5RowResidual f n p z = 0 := by
      intro z
      have h := hp z
      unfold v5RowResidual at h
      rw [Finset.sum_range_succ] at h
      simpa only [htop, map_zero, zero_mul, add_zero] using h
    intro k hk
    by_cases hkn : k ≤ n
    · exact ih (by omega) hsmall k hkn
    · simpa [show k = n+1 by omega] using htop

#print axioms v5_remainder_eq_zero_of_minimal
#print axioms v5_triangular_polynomial_pseudoDivide
#print axioms v5_triangular_pseudoDivide_top
/-- Pseudo-division by a polynomial operator preserves the coefficient
field. Only the finite support of the input row is used. -/
theorem v5_polynomial_pseudoDivide {K : Type*} [Field K]
    (m r : ℕ) (p q : ℕ → Polynomial K) (hq : q m ≠ 0) :
    ∃ b R : ℕ → Polynomial K,
      b r = (q m)^r * p (m+r) ∧
      (∀ k, m ≤ k → R k = 0) ∧
      ∀ k ≤ m+r, (q m)^(r+1) * p k = v5ComposePolynomialRows b q r m k + R k := by
  let T := fun j => v5TruncatePolynomialRow (v5IteratePolynomialRow q m j) (m+j)
  let P := v5TruncatePolynomialRow p (m+r)
  have ht : ∀ j, T j (m+j) = q m := by
    intro j
    simp [T, v5TruncatePolynomialRow, v5_iteratePolynomialRow_top]
  have hs : ∀ j k, m+j < k → T j k = 0 := by
    intro j k hk
    simp [T, v5TruncatePolynomialRow, Nat.not_le.mpr hk]
  have hp : ∀ k, m+r < k → P k = 0 := by
    intro k hk
    simp [P, v5TruncatePolynomialRow, Nat.not_le.mpr hk]
  obtain ⟨b, R, _, hR, heq⟩ := v5_triangular_polynomial_pseudoDivide m r (q m) T ht hs P hp
  have hb := v5_triangular_pseudoDivide_top m r (q m) hq T ht hs P b R hR heq
  refine ⟨b, R, ?_, hR, ?_⟩
  · simpa [P, v5TruncatePolynomialRow] using hb
  · intro k hk
    simpa [P, v5TruncatePolynomialRow, hk, v5ComposePolynomialRows, T] using heq k

#print axioms v5_polynomial_pseudoDivide
private theorem v5_remainder_cutoff {K : Type*} [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (R : ℕ → Polynomial K) (z : ℂ)
    {m n : ℕ} (hmn : m ≤ n) (hR : ∀ k, m < k → R k = 0) :
    v5RowResidual f n R z = v5RowResidual f m R z := by
  unfold v5RowResidual
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmn))
  intro k _ hk
  have hh : m < k := by
    by_contra! nh
    exact hk (Finset.mem_range.mpr (by omega))
  rw [hR k hh, map_zero, zero_mul]

/-- For an entire function, its minimal-order annihilator right-divides
any higher polynomial annihilator, up to a nonzero polynomial scale. -/
theorem v5_minimal_polynomial_right_factor {K : Type*} [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) (m r : ℕ)
    (p q : ℕ → Polynomial K) (hp : p (m+r) ≠ 0) (hq : q m ≠ 0)
    (hp0 : ∀ z, v5RowResidual f (m+r) p z = 0)
    (hq0 : ∀ z, v5RowResidual f m q z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder K f l) :
    ∃ b : ℕ → Polynomial K, b r ≠ 0 ∧
      ∀ k ≤ m+r, v5ComposePolynomialRows b q r m k = (q m)^(r+1) * p k := by
  obtain ⟨b, R, hb, hR, hdiv⟩ := v5_polynomial_pseudoDivide m r p q hq
  have hR0 : ∀ z, v5RowResidual f (m+r) R z = 0 := by
    intro z
    have hcomp := v5_polynomialRows_compose_action b q r m isOpen_univ
      (fun w _ => hf w) (Set.mem_univ z)
    have hq' : v5RowResidual f m q = (0 : ℂ → ℂ) := funext hq0
    have hz (k : ℕ) : iteratedDeriv k (0 : ℂ → ℂ) = 0 := by
      induction k with
      | zero => rw [iteratedDeriv_zero]
      | succ k ih => rw [iteratedDeriv_succ, ih]; ext; simp
    rw [hq'] at hcomp
    have hc0 : v5RowResidual f (m+r) (v5ComposePolynomialRows b q r m) z = 0 := by
      rw [← hcomp]
      simp [v5RowResidual, hz]
    have hscale :
        (Polynomial.eval₂RingHom (algebraMap K ℂ) z) ((q m)^(r+1)) *
          v5RowResidual f (m+r) p z =
        v5RowResidual f (m+r) (v5ComposePolynomialRows b q r m) z +
          v5RowResidual f (m+r) R z := by
      unfold v5RowResidual
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      rw [← mul_assoc, ← map_mul, hdiv k (by omega), map_add, add_mul]
    simpa only [hp0, hc0, mul_zero, zero_add] using hscale.symm
  have hzero (k : ℕ) : R k = 0 := by
    by_cases hk : m ≤ k
    · exact hR k hk
    · have hk' : k < m := by omega
      have hsmall : ∀ z, v5RowResidual f (m-1) R z = 0 := fun z =>
        (v5_remainder_cutoff f R z (by omega) (fun l hl => hR l (by omega))).symm.trans (hR0 z)
      exact v5_remainder_eq_zero_of_minimal hmin (show m-1 < m by omega) R hsmall k (by omega)
  refine ⟨b, fun h => (mul_ne_zero (pow_ne_zero _ hq) hp) (hb.symm.trans h), ?_⟩
  intro k hk
  simpa only [hzero k, add_zero] using (hdiv k hk).symm

#print axioms v5_minimal_polynomial_right_factor
end StrictEUnit
