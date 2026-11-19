import PolynomialClearedCoefficientRecurrence
import OrdinaryPointHouseBounds

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- A finite coefficient sum from the SAME polynomial system. -/
def clearedSystemTailNorm (t : Polynomial ℂ) (D : ℕ) : ℝ :=
  ∑ k : Fin D, ‖t.coeff (k.val+1)‖

def clearedSystemMatrixNorm {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) : ℝ :=
  ∑ i : Fin r, ∑ l : Fin r, ∑ k : Fin (D+1),
    ‖(U i l).coeff k.val‖

theorem clearedSystemTailNorm_nonneg (t : Polynomial ℂ) (D : ℕ) :
    0 ≤ clearedSystemTailNorm t D := by
  exact Finset.sum_nonneg (fun k hk => norm_nonneg _)

theorem clearedSystemMatrixNorm_nonneg {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) :
    0 ≤ clearedSystemMatrixNorm U D := by
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun l hl =>
    Finset.sum_nonneg (fun k hk => norm_nonneg _)))

theorem clearedSystemMatrixNorm_row_le {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) (i : Fin r) :
    (∑ l : Fin r, ∑ k : Fin (D+1), ‖(U i l).coeff k.val‖) ≤
      clearedSystemMatrixNorm U D := by
  classical
  unfold clearedSystemMatrixNorm
  let f : Fin r → ℝ := fun a => ∑ l : Fin r, ∑ k : Fin (D+1),
    ‖(U a l).coeff k.val‖
  have hf : ∀ a ∈ (Finset.univ : Finset (Fin r)), 0 ≤ f a := by
    intro a ha
    exact Finset.sum_nonneg (fun l hl => Finset.sum_nonneg (fun k hk =>
      norm_nonneg ((U a l).coeff k.val)))
  exact Finset.single_le_sum (s := Finset.univ) (f := f) hf (Finset.mem_univ i)

theorem clearedSystem_complex_matrix_sum_norm {r : ℕ}
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries ℂ))
    (C : ℝ) (hC : 1 ≤ C) (n D : ℕ)
    (hprev : ∀ m, m ≤ n → ∀ i j,
      ‖(PowerSeries.coeff ℂ m (Z i j))‖ ≤ C^n) (i j : Fin r) :
    ‖(∑ l : Fin r, ∑ k : Fin (D+1), if k.val ≤ n then
      (U i l).coeff k.val * PowerSeries.coeff ℂ (n-k.val) (Z l j) else 0)‖ ≤
        clearedSystemMatrixNorm U D * C^n := by
  classical
  have hCn : 0 ≤ C^n := pow_nonneg (le_trans zero_le_one hC) n
  calc
    _ ≤ ∑ l : Fin r, ∑ k : Fin (D+1),
        ‖(U i l).coeff k.val‖ * C^n := by
      apply norm_sum_le_of_le
      intro l hl
      apply norm_sum_le_of_le
      intro k hk
      by_cases hkn : k.val ≤ n
      · simp only [hkn, if_true, norm_mul]
        exact mul_le_mul le_rfl (hprev _ (Nat.sub_le _ _) _ _)
          (norm_nonneg _) (norm_nonneg _)
      · simp only [hkn, if_false, norm_zero]
        exact mul_nonneg (norm_nonneg _) hCn
    _ = (∑ l : Fin r, ∑ k : Fin (D+1),
        ‖(U i l).coeff k.val‖) * C^n := by
      simp only [Finset.sum_mul]
    _ ≤ clearedSystemMatrixNorm U D * C^n := by
      apply mul_le_mul_of_nonneg_right _ hCn
      exact clearedSystemMatrixNorm_row_le U D i

theorem clearedSystem_complex_tail_sum_norm {r : ℕ}
    (t : Polynomial ℂ) (Z : Matrix (Fin r) (Fin r) (PowerSeries ℂ))
    (C : ℝ) (hC : 1 ≤ C) (n D : ℕ)
    (hprev : ∀ m, m ≤ n → ∀ i j,
      ‖(PowerSeries.coeff ℂ m (Z i j))‖ ≤ C^n) (i j : Fin r) :
    ‖(∑ k : Fin D, if k.val+1 ≤ n then
      t.coeff (k.val+1) * (PowerSeries.coeff ℂ (n-(k.val+1)+1) (Z i j) *
        ((n-(k.val+1)+1 : ℕ) : ℂ)) else 0)‖ ≤
        clearedSystemTailNorm t D * C^n * (n+1:ℝ) := by
  classical
  have hCn : 0 ≤ C^n := pow_nonneg (le_trans zero_le_one hC) n
  have hN : 0 < (n+1:ℝ) := by positivity
  calc
    _ ≤ ∑ k : Fin D, ‖t.coeff (k.val+1)‖ * C^n * (n+1:ℝ) := by
      apply norm_sum_le_of_le
      intro k hk
      by_cases hkn : k.val+1 ≤ n
      · simp only [hkn, if_true, norm_mul, Complex.norm_natCast]
        have hm : n-(k.val+1)+1 ≤ n := by omega
        have hfac : ((n-(k.val+1)+1 : ℕ):ℝ) ≤ (n+1:ℝ) := by
          exact_mod_cast (show n-(k.val+1)+1 ≤ n+1 by omega)
        calc
          _ ≤ ‖t.coeff (k.val+1)‖ *
              (C^n * (n+1:ℝ)) :=
            mul_le_mul le_rfl
              (mul_le_mul (hprev _ hm i j) hfac (by positivity) hCn)
              (by positivity) (norm_nonneg _)
          _ = _ := by ring
      · simp only [hkn, if_false, norm_zero]
        exact mul_nonneg (mul_nonneg (norm_nonneg _) hCn) (le_of_lt hN)
    _ = _ := by simp only [clearedSystemTailNorm, Finset.sum_mul]

/-- One recurrence step: the integer derivative factors are bounded by n+1
before cancelling that positive factor. No coefficient house bound is assumed. -/
theorem clearedPolynomialSystem_complex_step {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries ℂ))
    (ht0 : t.coeff 0 ≠ 0) (D : ℕ) (htdeg : t.natDegree ≤ D)
    (hUdeg : ∀ i l, (U i l).natDegree ≤ D)
    (hode : ∀ i j, (t : PowerSeries ℂ) * PowerSeries.derivative ℂ (Z i j) =
      ∑ l : Fin r, (U i l : PowerSeries ℂ) * Z l j)
    (C : ℝ) (hC : 1 ≤ C) (n : ℕ)
    (hprev : ∀ m, m ≤ n → ∀ i j,
      ‖(PowerSeries.coeff ℂ m (Z i j))‖ ≤ C^n) (i j : Fin r) :
    ‖(PowerSeries.coeff ℂ (n+1) (Z i j))‖ ≤
      ‖(t.coeff 0)⁻¹‖ *
        (clearedSystemTailNorm t D + clearedSystemMatrixNorm U D) * C^n := by
  classical
  let R := ∑ l : Fin r, ∑ k : Fin (D+1), if k.val ≤ n then
    (U i l).coeff k.val * PowerSeries.coeff ℂ (n-k.val) (Z l j) else 0
  let S := ∑ k : Fin D, if k.val+1 ≤ n then
    t.coeff (k.val+1) * (PowerSeries.coeff ℂ (n-(k.val+1)+1) (Z i j) *
      ((n-(k.val+1)+1 : ℕ) : ℂ)) else 0
  let A := ‖(t.coeff 0)⁻¹‖
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCn : 0 ≤ C^n := pow_nonneg hC0 n
  have hN : 0 < (n+1:ℝ) := by positivity
  have hr : ‖R‖ ≤ clearedSystemMatrixNorm U D * C^n :=
    clearedSystem_complex_matrix_sum_norm U Z C hC n D hprev i j
  have hs : ‖S‖ ≤ clearedSystemTailNorm t D * C^n * (n+1:ℝ) :=
    clearedSystem_complex_tail_sum_norm t Z C hC n D hprev i j
  have hrec : (n+1:ℂ) * PowerSeries.coeff ℂ (n+1) (Z i j) =
      (t.coeff 0)⁻¹ * (R-S) := by
    have he := clearedPolynomialSystem_coeff_recurrence t U Z D htdeg hUdeg hode n i j
    calc
      _ = (t.coeff 0)⁻¹ *
          (t.coeff 0 * (n+1:ℂ) * PowerSeries.coeff ℂ (n+1) (Z i j)) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      _ = _ := congrArg (fun x : ℂ => (t.coeff 0)⁻¹ * x) he
  have hnorm : (n+1:ℝ) * ‖(PowerSeries.coeff ℂ (n+1) (Z i j))‖ ≤
      A * (clearedSystemMatrixNorm U D * C^n +
        clearedSystemTailNorm t D * C^n * (n+1:ℝ)) := by
    have hm := hrec
    simp only [Nat.cast_add,Nat.cast_one] at hm
    calc
      _ = ‖((t.coeff 0)⁻¹) * (R-S)‖ := by
        rw [← hm, norm_mul]
        have hnat : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
          simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n+1)
        rw [hnat]
      _ ≤ A * (‖R‖ + ‖S‖) := by
        rw [norm_mul]
        exact mul_le_mul le_rfl (norm_sub_le _ _)
          (norm_nonneg _) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hr hs) (norm_nonneg _)
  have hg : clearedSystemMatrixNorm U D * C^n ≤
      clearedSystemMatrixNorm U D * C^n * (n+1:ℝ) := by
    have h1 : (1:ℝ) ≤ (n+1:ℝ) := by have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1
      (mul_nonneg (clearedSystemMatrixNorm_nonneg U D) hCn)
  have htotal : (n+1:ℝ) * ‖(PowerSeries.coeff ℂ (n+1) (Z i j))‖ ≤
      (n+1:ℝ) * (A * (clearedSystemTailNorm t D + clearedSystemMatrixNorm U D) * C^n) := by
    calc
      _ ≤ _ := hnorm
      _ ≤ A * (clearedSystemMatrixNorm U D * C^n * (n+1:ℝ) +
          clearedSystemTailNorm t D * C^n * (n+1:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hg _)
          (norm_nonneg _)
      _ = _ := by ring
  exact (mul_le_mul_left hN).1 htotal

end StrictEUnit
end
