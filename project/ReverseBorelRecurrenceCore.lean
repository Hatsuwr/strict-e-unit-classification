import BorelCoefficientPolynomialRecurrence

/-! NEW SOURCE-ONLY, UNCOMPILED. Explicit normal-order tuple and coefficient
identities for reversing a polynomial recurrence. No abstract operator
nonvanishing or arithmetic-family assertion is substituted for tuple nonzero. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The low-index case vanishes on BOTH sides, so no boundary polynomial is
silently discarded. This also covers derivative order and shift zero. -/
theorem borel_coeff_shifted_derivative (a : ℕ → K) (n j t : ℕ) :
    PowerSeries.coeff K n (PowerSeries.X ^ t *
      (PowerSeries.derivative K)^[j+t] (PowerSeries.mk a)) =
      (descPochhammer K (j+t)).eval ((n+j : ℕ) : K) * a (n+j) := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases ht : t ≤ n
  · rw [if_pos ht, stage26_coeff_iterate_derivative, PowerSeries.coeff_mk]
    have hi : n-t+(j+t) = n+j := by omega
    rw [hi]
  · rw [if_neg ht, descPochhammer_eval_coe_nat_of_lt (by omega : n+j < j+t), zero_mul]

/-- The polynomial tuple is explicitly grouped by derivative order. -/
def borelNormalTuple (r L : ℕ) (b : Fin (r+1) → Fin (L+1) → K)
    (i : Fin (r+L+1)) : Polynomial K :=
  ∑ j, ∑ t, if j.val+t.val = i.val then Polynomial.monomial t.val (b j t) else 0

/-- A coefficient of the normal-order tuple recovers each original array entry.
At fixed order i=j+t and power t, no other pair can contribute. -/
theorem borelNormalTuple_coeff (r L : ℕ) (b : Fin (r+1) → Fin (L+1) → K)
    (j : Fin (r+1)) (t : Fin (L+1)) :
    (borelNormalTuple r L b ⟨j.val+t.val, by omega⟩).coeff t.val = b j t := by
  simp only [borelNormalTuple, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl, Polynomial.coeff_monomial_same]
    · intro t' ht' hne
      have htne : t'.val ≠ t.val := fun h => hne (Fin.ext h)
      have hsum : j.val+t'.val ≠ j.val+t.val := by omega
      rw [if_neg hsum, Polynomial.coeff_zero]
    · intro h
      exact (h (Finset.mem_univ t)).elim
  · intro j' hj' hne
    apply Finset.sum_eq_zero
    intro t' ht'
    by_cases heq : j'.val+t'.val = j.val+t.val
    · have htne : t'.val ≠ t.val := by
        intro htval
        apply hne
        apply Fin.ext
        omega
      rw [if_pos heq, Polynomial.coeff_monomial, if_neg htne]
    · rw [if_neg heq, Polynomial.coeff_zero]
  · intro h
    exact (h (Finset.mem_univ j)).elim

theorem borelNormalTuple_nonzero (r L : ℕ) (b : Fin (r+1) → Fin (L+1) → K)
    (hb : ∃ j t, b j t ≠ 0) : ∃ i, borelNormalTuple r L b i ≠ 0 := by
  obtain ⟨j,t,hb⟩ := hb
  refine ⟨⟨j.val+t.val, by omega⟩, ?_⟩
  intro hz
  have h := congrArg (fun P : Polynomial K => P.coeff t.val) hz
  dsimp only at h
  rw [borelNormalTuple_coeff, Polynomial.coeff_zero] at h
  exact hb h

/-- Finite diagonal regrouping, including r=L=0. -/
theorem borel_sum_diagonal {R : Type*} [AddCommMonoid R]
    (r L : ℕ) (f : Fin (r+1) → Fin (L+1) → R) :
    (∑ i : Fin (r+L+1), ∑ j, ∑ t,
      if j.val+t.val = i.val then f j t else 0) = ∑ j, ∑ t, f j t := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  let i0 : Fin (r+L+1) := ⟨j.val+t.val, by omega⟩
  rw [Finset.sum_eq_single i0]
  · change (if j.val+t.val = j.val+t.val then f j t else 0) = f j t
    rw [if_pos rfl]
  · intro i hi hne
    have hn : j.val+t.val ≠ i.val := by
      intro h
      exact hne (Fin.ext h.symm)
    rw [if_neg hn]
  · intro h
    exact (h (Finset.mem_univ i0)).elim

/-- The actual grouped differential expression has precisely the double sum
of falling-factorial contributions, at EVERY n. -/
theorem borelNormalTuple_action_coeff (a : ℕ → K) (r L : ℕ)
    (b : Fin (r+1) → Fin (L+1) → K) (n : ℕ) :
    PowerSeries.coeff K n (∑ i, (borelNormalTuple r L b i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] (PowerSeries.mk a)) =
      ∑ j, ∑ t, b j t * (descPochhammer K (j.val+t.val)).eval ((n+j.val : ℕ) : K) *
        a (n+j.val) := by
  have hmono (c : K) (t i : ℕ) : PowerSeries.coeff K n
      ((Polynomial.monomial t c : Polynomial K) *
        (PowerSeries.derivative K)^[i] (PowerSeries.mk a) : PowerSeries K) =
      c * PowerSeries.coeff K n (PowerSeries.X ^ t *
        (PowerSeries.derivative K)^[i] (PowerSeries.mk a)) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      mul_assoc, PowerSeries.coeff_C_mul]
  have hterm (i : Fin (r+L+1)) : PowerSeries.coeff K n
      ((borelNormalTuple r L b i : PowerSeries K) *
        (PowerSeries.derivative K)^[i.val] (PowerSeries.mk a)) =
      ∑ j, ∑ t, if j.val+t.val = i.val then
        b j t * (descPochhammer K (j.val+t.val)).eval ((n+j.val : ℕ) : K) * a (n+j.val)
        else 0 := by
    change PowerSeries.coeff K n
      ((Polynomial.coeToPowerSeries.ringHom (∑ j, ∑ t,
        if j.val+t.val = i.val then Polynomial.monomial t.val (b j t) else 0)) * _) = _
    simp only [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro t ht
    by_cases heq : j.val+t.val = i.val
    · simp only [if_pos heq, Polynomial.coeToPowerSeries.ringHom_apply]
      rw [hmono, ← heq, borel_coeff_shifted_derivative]
      ring
    · simp only [if_neg heq, map_zero, zero_mul]
  rw [map_sum]
  simp_rw [hterm]
  exact borel_sum_diagonal r L _

/-- Split the shifted falling factorial into its initial j factors and its
remaining t factors. -/
theorem borel_descPochhammer_split (n j t : ℕ) :
    (descPochhammer K (j+t)).eval ((n+j : ℕ) : K) =
      (descPochhammer K j).eval ((n+j : ℕ) : K) *
        (descPochhammer K t).eval (n : K) := by
  rw [← descPochhammer_mul K j t, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast, Nat.cast_add,
    add_sub_cancel_right]

/-- Exact initial-factor evaluation, with nonzero factorial denominator. -/
theorem borel_descPochhammer_factorial_ratio (n j : ℕ) :
    (descPochhammer K j).eval ((n+j : ℕ) : K) =
      ((n+j).factorial : K) / (n.factorial : K) := by
  rw [descPochhammer_eval_eq_descFactorial]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).mpr
  have h := Nat.factorial_mul_descFactorial (show j ≤ n+j by omega)
  have hsub : n+j-j=n := by omega
  rw [hsub] at h
  have hk : (n.factorial : K) * ((n+j).descFactorial j : K) = ((n+j).factorial : K) := by
    exact_mod_cast h
  simpa only [mul_comm] using hk

/-- Normal-ordering from a finite falling-factorial expansion produces a
NONZERO ODE tuple for the same ordinary series. The expansion will be supplied
by the separate uniform-basis helper, not an analytic or operator assumption. -/
theorem recurrence_to_ordinary_ode_of_expansion
    (a : ℕ → K) (r : ℕ) (Q : Fin (r+1) → Polynomial K)
    (hQ : ∃ j, Q j ≠ 0)
    (hrec : ∀ n : ℕ, (∑ j, (Q j).eval (n : K) * a (n+j.val)) = 0)
    (L : ℕ) (b : Fin (r+1) → Fin (L+1) → K)
    (hexp : ∀ j, Q j * borelFactorialMultiplier j.val (r-j.val) =
      ∑ t, Polynomial.C (b j t) * descPochhammer K t.val) :
    (∃ i, borelNormalTuple r L b i ≠ 0) ∧
      (∑ i, (borelNormalTuple r L b i : PowerSeries K) *
        (PowerSeries.derivative K)^[i.val] (PowerSeries.mk a)) = 0 := by
  have hb : ∃ j t, b j t ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨j,hj⟩ := hQ
    have hz : Q j * borelFactorialMultiplier j.val (r-j.val) = 0 := by
      rw [hexp j]
      simp only [h, Polynomial.C_0, zero_mul, Finset.sum_const_zero]
    exact (mul_ne_zero hj (borelFactorialMultiplier_ne_zero j.val (r-j.val))) hz
  refine ⟨borelNormalTuple_nonzero r L b hb, ?_⟩
  apply PowerSeries.ext
  intro n
  rw [borelNormalTuple_action_coeff, map_zero]
  have hj (j : Fin (r+1)) :
      (∑ t, b j t * (descPochhammer K (j.val+t.val)).eval ((n+j.val : ℕ) : K) * a (n+j.val)) =
      (((n+r).factorial : K) / (n.factorial : K)) * (Q j).eval (n : K) * a (n+j.val) := by
    have he := congrArg (fun P : Polynomial K => P.eval (n : K)) (hexp j)
    simp only [Polynomial.eval_mul, Polynomial.eval_finset_sum, Polynomial.eval_C] at he
    calc
      _ = (descPochhammer K j.val).eval ((n+j.val : ℕ) : K) *
          (∑ t, b j t * (descPochhammer K t.val).eval (n : K)) * a (n+j.val) := by
        simp_rw [borel_descPochhammer_split]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = _ := by
        rw [← he, borel_descPochhammer_factorial_ratio, borelFactorialMultiplier_eval_ratio]
        have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hnj : ((n+j.val).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        field_simp
        <;> ring
  simp_rw [hj]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, hrec, mul_zero]

end StrictEUnit
end
