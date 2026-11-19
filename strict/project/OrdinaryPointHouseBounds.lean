import PolynomialClearedCoefficientRecurrence
import IntegralNormHouse

noncomputable section
open scoped NumberField BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem conjugate_norm_le_house (σ : K →+* ℂ) (x : K) :
    ‖σ x‖ ≤ NumberField.house x :=
  (NumberField.canonicalEmbedding.norm_le_iff x (NumberField.house x)).1 le_rfl σ

/-- A finite coefficient sum from the SAME polynomial system. -/
def clearedSystemTailHouse (t : Polynomial K) (D : ℕ) : ℝ :=
  ∑ k : Fin D, NumberField.house (t.coeff (k.val+1))

def clearedSystemMatrixHouse {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (D : ℕ) : ℝ :=
  ∑ i : Fin r, ∑ l : Fin r, ∑ k : Fin (D+1),
    NumberField.house ((U i l).coeff k.val)

theorem clearedSystemTailHouse_nonneg (t : Polynomial K) (D : ℕ) :
    0 ≤ clearedSystemTailHouse t D := by
  exact Finset.sum_nonneg (fun k hk => NumberField.house_nonneg _)

theorem clearedSystemMatrixHouse_nonneg {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (D : ℕ) :
    0 ≤ clearedSystemMatrixHouse U D := by
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun l hl =>
    Finset.sum_nonneg (fun k hk => NumberField.house_nonneg _)))

theorem clearedSystemMatrixHouse_row_le {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (D : ℕ) (i : Fin r) :
    (∑ l : Fin r, ∑ k : Fin (D+1), NumberField.house ((U i l).coeff k.val)) ≤
      clearedSystemMatrixHouse U D := by
  classical
  unfold clearedSystemMatrixHouse
  let f : Fin r → ℝ := fun a => ∑ l : Fin r, ∑ k : Fin (D+1),
    NumberField.house ((U a l).coeff k.val)
  have hf : ∀ a ∈ (Finset.univ : Finset (Fin r)), 0 ≤ f a := by
    intro a ha
    exact Finset.sum_nonneg (fun l hl => Finset.sum_nonneg (fun k hk =>
      NumberField.house_nonneg ((U a l).coeff k.val)))
  exact Finset.single_le_sum (s := Finset.univ) (f := f) hf (Finset.mem_univ i)

theorem clearedSystem_conjugate_matrix_sum_norm {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (σ : K →+* ℂ) (C : ℝ) (hC : 1 ≤ C) (n D : ℕ)
    (hprev : ∀ m, m ≤ n → ∀ i j,
      ‖σ (PowerSeries.coeff K m (Z i j))‖ ≤ C^n) (i j : Fin r) :
    ‖σ (∑ l : Fin r, ∑ k : Fin (D+1), if k.val ≤ n then
      (U i l).coeff k.val * PowerSeries.coeff K (n-k.val) (Z l j) else 0)‖ ≤
        clearedSystemMatrixHouse U D * C^n := by
  classical
  have hCn : 0 ≤ C^n := pow_nonneg (le_trans zero_le_one hC) n
  simp only [map_sum]
  calc
    _ ≤ ∑ l : Fin r, ∑ k : Fin (D+1),
        NumberField.house ((U i l).coeff k.val) * C^n := by
      apply norm_sum_le_of_le
      intro l hl
      apply norm_sum_le_of_le
      intro k hk
      by_cases hkn : k.val ≤ n
      · simp only [hkn, if_true, map_mul, norm_mul]
        exact mul_le_mul (conjugate_norm_le_house σ _) (hprev _ (Nat.sub_le _ _) _ _)
          (norm_nonneg _) (NumberField.house_nonneg _)
      · simp only [hkn, if_false, map_zero, norm_zero]
        exact mul_nonneg (NumberField.house_nonneg _) hCn
    _ = (∑ l : Fin r, ∑ k : Fin (D+1),
        NumberField.house ((U i l).coeff k.val)) * C^n := by
      simp only [Finset.sum_mul]
    _ ≤ clearedSystemMatrixHouse U D * C^n := by
      apply mul_le_mul_of_nonneg_right _ hCn
      exact clearedSystemMatrixHouse_row_le U D i

theorem clearedSystem_conjugate_tail_sum_norm {r : ℕ}
    (t : Polynomial K) (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (σ : K →+* ℂ) (C : ℝ) (hC : 1 ≤ C) (n D : ℕ)
    (hprev : ∀ m, m ≤ n → ∀ i j,
      ‖σ (PowerSeries.coeff K m (Z i j))‖ ≤ C^n) (i j : Fin r) :
    ‖σ (∑ k : Fin D, if k.val+1 ≤ n then
      t.coeff (k.val+1) * (PowerSeries.coeff K (n-(k.val+1)+1) (Z i j) *
        ((n-(k.val+1)+1 : ℕ) : K)) else 0)‖ ≤
        clearedSystemTailHouse t D * C^n * (n+1:ℝ) := by
  classical
  have hCn : 0 ≤ C^n := pow_nonneg (le_trans zero_le_one hC) n
  have hN : 0 < (n+1:ℝ) := by positivity
  simp only [map_sum]
  calc
    _ ≤ ∑ k : Fin D, NumberField.house (t.coeff (k.val+1)) * C^n * (n+1:ℝ) := by
      apply norm_sum_le_of_le
      intro k hk
      by_cases hkn : k.val+1 ≤ n
      · simp only [hkn, if_true, map_mul, map_natCast, norm_mul, Complex.norm_natCast]
        have hm : n-(k.val+1)+1 ≤ n := by omega
        have hfac : ((n-(k.val+1)+1 : ℕ):ℝ) ≤ (n+1:ℝ) := by
          exact_mod_cast (show n-(k.val+1)+1 ≤ n+1 by omega)
        calc
          _ ≤ NumberField.house (t.coeff (k.val+1)) *
              (C^n * (n+1:ℝ)) :=
            mul_le_mul (conjugate_norm_le_house σ _)
              (mul_le_mul (hprev _ hm i j) hfac (by positivity) hCn)
              (by positivity) (NumberField.house_nonneg _)
          _ = _ := by ring
      · simp only [hkn, if_false, map_zero, norm_zero]
        exact mul_nonneg (mul_nonneg (NumberField.house_nonneg _) hCn) (le_of_lt hN)
    _ = _ := by simp only [clearedSystemTailHouse, Finset.sum_mul]

/-- One recurrence step: the integer derivative factors are bounded by n+1
before cancelling that positive factor. No coefficient house bound is assumed. -/
theorem clearedPolynomialSystem_conjugate_step {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (ht0 : t.coeff 0 ≠ 0) (D : ℕ) (htdeg : t.natDegree ≤ D)
    (hUdeg : ∀ i l, (U i l).natDegree ≤ D)
    (hode : ∀ i j, (t : PowerSeries K) * PowerSeries.derivative K (Z i j) =
      ∑ l : Fin r, (U i l : PowerSeries K) * Z l j)
    (σ : K →+* ℂ) (C : ℝ) (hC : 1 ≤ C) (n : ℕ)
    (hprev : ∀ m, m ≤ n → ∀ i j,
      ‖σ (PowerSeries.coeff K m (Z i j))‖ ≤ C^n) (i j : Fin r) :
    ‖σ (PowerSeries.coeff K (n+1) (Z i j))‖ ≤
      NumberField.house ((t.coeff 0)⁻¹) *
        (clearedSystemTailHouse t D + clearedSystemMatrixHouse U D) * C^n := by
  classical
  let R := ∑ l : Fin r, ∑ k : Fin (D+1), if k.val ≤ n then
    (U i l).coeff k.val * PowerSeries.coeff K (n-k.val) (Z l j) else 0
  let S := ∑ k : Fin D, if k.val+1 ≤ n then
    t.coeff (k.val+1) * (PowerSeries.coeff K (n-(k.val+1)+1) (Z i j) *
      ((n-(k.val+1)+1 : ℕ) : K)) else 0
  let A := NumberField.house ((t.coeff 0)⁻¹)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCn : 0 ≤ C^n := pow_nonneg hC0 n
  have hN : 0 < (n+1:ℝ) := by positivity
  have hr : ‖σ R‖ ≤ clearedSystemMatrixHouse U D * C^n :=
    clearedSystem_conjugate_matrix_sum_norm U Z σ C hC n D hprev i j
  have hs : ‖σ S‖ ≤ clearedSystemTailHouse t D * C^n * (n+1:ℝ) :=
    clearedSystem_conjugate_tail_sum_norm t Z σ C hC n D hprev i j
  have hrec : (n+1:K) * PowerSeries.coeff K (n+1) (Z i j) =
      (t.coeff 0)⁻¹ * (R-S) := by
    have he := clearedPolynomialSystem_coeff_recurrence t U Z D htdeg hUdeg hode n i j
    calc
      _ = (t.coeff 0)⁻¹ *
          (t.coeff 0 * (n+1:K) * PowerSeries.coeff K (n+1) (Z i j)) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      _ = _ := congrArg (fun x : K => (t.coeff 0)⁻¹ * x) he
  have hnorm : (n+1:ℝ) * ‖σ (PowerSeries.coeff K (n+1) (Z i j))‖ ≤
      A * (clearedSystemMatrixHouse U D * C^n +
        clearedSystemTailHouse t D * C^n * (n+1:ℝ)) := by
    have hm := congrArg σ hrec
    simp only [map_mul, map_add, map_natCast, map_one] at hm
    calc
      _ = ‖σ ((t.coeff 0)⁻¹) * σ (R-S)‖ := by
        rw [← hm, norm_mul]
        have hnat : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
          simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n+1)
        rw [hnat]
      _ ≤ A * (‖σ R‖ + ‖σ S‖) := by
        rw [norm_mul, map_sub]
        exact mul_le_mul (conjugate_norm_le_house σ _) (norm_sub_le _ _)
          (norm_nonneg _) (NumberField.house_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hr hs) (NumberField.house_nonneg _)
  have hg : clearedSystemMatrixHouse U D * C^n ≤
      clearedSystemMatrixHouse U D * C^n * (n+1:ℝ) := by
    have h1 : (1:ℝ) ≤ (n+1:ℝ) := by have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1
      (mul_nonneg (clearedSystemMatrixHouse_nonneg U D) hCn)
  have htotal : (n+1:ℝ) * ‖σ (PowerSeries.coeff K (n+1) (Z i j))‖ ≤
      (n+1:ℝ) * (A * (clearedSystemTailHouse t D + clearedSystemMatrixHouse U D) * C^n) := by
    calc
      _ ≤ _ := hnorm
      _ ≤ A * (clearedSystemMatrixHouse U D * C^n * (n+1:ℝ) +
          clearedSystemTailHouse t D * C^n * (n+1:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hg _)
          (NumberField.house_nonneg _)
      _ = _ := by ring
  exact (mul_le_mul_left hN).1 htotal

end StrictEUnit
end
