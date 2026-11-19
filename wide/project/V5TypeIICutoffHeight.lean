import TypeIIExponentialDenominatorBounds

noncomputable section
namespace StrictEUnit
open scoped BigOperators NumberField

/-- The literal lift consumes one factor of the prefix height and two
from the balanced Padé denominator. No global growth premise is used. -/
theorem v5_typeII_lift_height_factor (r e N : ℕ) (HT B H : ℝ) :
    typeIIIntegralLiftMatrixBound r e N HT (B * H^2) H =
      typeIIIntegralLiftMatrixBound r e N HT B 1 * H^3 := by
  unfold typeIIIntegralLiftMatrixBound
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual determinant estimate has a fixed exponential part and
exactly a fixed power of the pointwise prefix height. -/
theorem v5_typeII_determinant_bound_cutoff_height (r e τ t : ℕ) (HT B H : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hHT : 1 ≤ HT) (hB : 1 ≤ B) (hH : 1 ≤ H) :
    1 ≤ typeIIDeterminantExponentialBase r e τ HT B 1 ∧
    (r.factorial:ℝ)*(((2*r*t-1+(r-1)*τ:ℕ)+1:ℝ)*
      typeIIIntegralLiftMatrixBound r e (2*r*t-1) HT (B^t * H^2) H)^r ≤
      (typeIIDeterminantExponentialBase r e τ HT B 1)^t * H^(3*r) := by
  obtain ⟨hbase,hdet⟩ := typeII_determinant_bound_exponential r e τ t HT B 1
    hr ht hHT hB le_rfl
  simp only [one_pow] at hdet
  refine ⟨hbase,?_⟩
  rw [v5_typeII_lift_height_factor]
  calc
    _ = ((r.factorial:ℝ)*(((2*r*t-1+(r-1)*τ:ℕ)+1:ℝ)*
        typeIIIntegralLiftMatrixBound r e (2*r*t-1) HT (B^t) 1)^r) *
        H^(3*r) := by rw [pow_mul, ← mul_assoc, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hdet (pow_nonneg (zero_le_one.trans hH) _)

/-- A balanced finite Padé denominator with a pointwise height bound.
The same approximation gives contact and the height used in the lift. -/
theorem v5_exists_cutoff_height_typeII_pade
    (K : Type*) [Field K] [NumberField K] (r : ℕ) (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (t δ : ℕ) (f : Fin r → PowerSeries K)
      (b : Fin r → ℕ → 𝓞 K) (H : ℝ),
      0 < t → 0 < δ → 1 ≤ H → (δ : ℝ) ≤ H →
      (∀ j n, n ≤ (2*r*t-1)+t →
        (b j n : K) = (δ : K)*PowerSeries.coeff K n (f j)) →
      (∀ j n, n ≤ (2*r*t-1)+t → NumberField.house (b j n : K) ≤ H) →
      ∃ Q : Polynomial (𝓞 K), ∃ P : Fin r → Polynomial (𝓞 K),
        Q ≠ 0 ∧ Q.natDegree ≤ 2*r*t-1 ∧ (∀ j, (P j).natDegree ≤ 2*r*t-1) ∧
        (∀ j n, n < (2*r*t-1)+t+1 → PowerSeries.coeff K n
          (((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f j) -
            ((P j).map (algebraMap (𝓞 K) K) : PowerSeries K)) = 0) ∧
        (∀ n, NumberField.house (Q.coeff n : K) ≤ A^t * H^2) := by
  obtain ⟨κ,hκ⟩ := exists_integral_typeII_pade K
  let J := max 1 (κ^2 * ((2*r : ℕ) : ℝ))
  have hJ : 1 ≤ J := le_max_left _ _
  refine ⟨2*J, one_le_mul_of_one_le_of_one_le (by norm_num) hJ, ?_⟩
  intro t δ f b H ht hδ hH hδH hb hh
  let N := 2*r*t-1
  have hdim : N+1 = 2*r*t := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hr) ht))
  have hs : r*t < N+1 := by rw [hdim]; nlinarith [Nat.mul_pos hr ht]
  obtain ⟨Q,P,hQ,hQN,hPN,_,hc,hQH,_⟩ :=
    hκ r N t δ f b H H hδ hs (zero_le_one.trans hH) hδH hb hh
  have he := typeII_balanced_kernel_bound κ H r t hr ht
  simp only [Nat.cast_add, Nat.cast_one, N] at hQH
  rw [he] at hQH
  refine ⟨Q,P,hQ,hQN,hPN,hc,?_⟩
  intro n
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hE : max 1 (κ^2 * ((2*r*t : ℕ) : ℝ) * H) ≤ J*(t:ℝ)*H := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hJ htR) hH
    · push_cast; rw [← mul_assoc (κ^2) (2 * (r:ℝ)) (t:ℝ)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show κ^2 * (2*r:ℝ) ≤ J by
            simpa only [J, Nat.cast_mul, Nat.cast_ofNat] using
              (le_max_right (1:ℝ) (κ^2*((2*r:ℕ):ℝ))))
          (Nat.cast_nonneg t)) (zero_le_one.trans hH)
  have htw : (t:ℝ) ≤ (2:ℝ)^t := by exact_mod_cast Nat.le_of_lt t.lt_two_pow_self
  have hpower : J*(t:ℝ) ≤ (2*J)^t := by
    rw [mul_pow, mul_comm ((2:ℝ)^t)]
    exact mul_le_mul (le_self_pow₀ hJ (Nat.ne_of_gt ht)) htw
      (Nat.cast_nonneg t) (pow_nonneg (zero_le_one.trans hJ) _)
  calc
    _ ≤ H * max 1 (κ^2 * ((2*r*t : ℕ) : ℝ) * H) := hQH n
    _ ≤ H * (J*(t:ℝ)*H) := mul_le_mul_of_nonneg_left hE (zero_le_one.trans hH)
    _ = (J*(t:ℝ))*H^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpower (sq_nonneg H)

#print axioms v5_typeII_lift_height_factor
#print axioms v5_typeII_determinant_bound_cutoff_height
#print axioms v5_exists_cutoff_height_typeII_pade
end StrictEUnit
end
