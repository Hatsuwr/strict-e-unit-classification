import V5BroadPowerArithmetic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

namespace StrictEUnit

private theorem v5_broad_tail_ratio {C η x : ℝ} (hC : 1 ≤ C)
    (hη : η ≤ 1/2) (hx : 1 ≤ x) (hlarge : (2*C)^2 ≤ x) :
    C * x^η / x ≤ 1/2 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ x^η := Real.rpow_nonneg hx0.le _
  have hy2 : (x^η)^2 ≤ x := by
    rw [← Real.rpow_mul_natCast hx0.le]
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show η*(2:ℝ) ≤ 1 by linarith)
  have hprod := mul_le_mul hlarge hy2 (sq_nonneg _) hx0.le
  have hxy : 2*C*x^η ≤ x := by
    have hC0 : 0 ≤ C := by linarith
    nlinarith [sq_nonneg (2*C*x^η+x)]
  apply (div_le_iff₀ hx0).mpr
  nlinarith

noncomputable def v5BroadTailMajorant (C η : ℝ) (k : ℕ) : ℝ :=
  C^(k+1) * (k.factorial : ℝ)^η / (k.factorial : ℝ)

theorem v5_broad_tail_majorant_step {C η : ℝ} (hC : 1 ≤ C)
    (hη : η ≤ 1/2) (k : ℕ) (hlarge : (2*C)^2 ≤ (k+1 : ℝ)) :
    v5BroadTailMajorant C η (k+1) ≤ v5BroadTailMajorant C η k * (1/2) := by
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (0 : ℝ) < k+1 := by positivity
  have he : v5BroadTailMajorant C η (k+1) =
      v5BroadTailMajorant C η k * (C*(k+1 : ℝ)^η/(k+1 : ℝ)) := by
    unfold v5BroadTailMajorant
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.mul_rpow hk1.le hk.le, pow_succ]
    field_simp
    ; ring
  rw [he]
  apply mul_le_mul_of_nonneg_left (v5_broad_tail_ratio hC hη (by linarith [Nat.cast_nonneg (α := ℝ) k]) hlarge)
  unfold v5BroadTailMajorant
  positivity

/-- The factorial-normalized tail has a geometric majorant with total
weight one, uniformly in every coefficient embedding. -/
theorem v5_broad_division_tail_term {C η : ℝ} (hC : 1 ≤ C)
    (hη : η ≤ 1/2) (n j : ℕ) (hlarge : (2*C)^2 ≤ (n+1 : ℝ)) :
    (n.factorial : ℝ) * C^(n+j+1+1) *
      ((n+j+1).factorial : ℝ)^η / ((n+j+1).factorial : ℝ) ≤
      C^(n+1)*(n.factorial : ℝ)^η*(1/2 : ℝ)^(j+1) := by
  have hgeom : ∀ k : ℕ, v5BroadTailMajorant C η (n+k) ≤
      v5BroadTailMajorant C η n * (1/2 : ℝ)^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ v5BroadTailMajorant C η (n+k)*(1/2) := by
          apply v5_broad_tail_majorant_step hC hη (n+k)
          have hnk : (n+1 : ℝ) ≤ ((n+k : ℕ) : ℝ)+1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
          exact hlarge.trans hnk
        _ ≤ (v5BroadTailMajorant C η n*(1/2 : ℝ)^k)*(1/2) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hb := mul_le_mul_of_nonneg_left (hgeom (j+1)) (show (0 : ℝ) ≤ n.factorial by positivity)
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hc : (n.factorial : ℝ)*v5BroadTailMajorant C η n =
      C^(n+1)*(n.factorial : ℝ)^η := by unfold v5BroadTailMajorant; field_simp
  rw [← mul_assoc, hc] at hb
  convert hb using 1; simp only [v5BroadTailMajorant, Nat.add_assoc]; ring

theorem v5_hasSum_half_tail : HasSum (fun j : ℕ => (1/2 : ℝ)^(j+1)) 1 := by
  have h := (hasSum_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ) < 1 by norm_num)).mul_left (1/2)
  convert h using 1
  · funext j
    rw [pow_succ]
    ring
  · norm_num

/-- Abstract norm form of the geometric tail estimate. -/
theorem v5_broad_division_tail_norm {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (s : E) (A : ℝ)
    (hs : HasSum u s) (hu : ∀ j, ‖u j‖ ≤ A*(1/2 : ℝ)^(j+1)) :
    ‖s‖ ≤ A := by
  have h := v5_hasSum_half_tail.mul_left A
  simpa only [mul_one] using hs.norm_le_of_bounded h hu

#print axioms v5_broad_tail_majorant_step
#print axioms v5_broad_division_tail_term
#print axioms v5_hasSum_half_tail
#print axioms v5_broad_division_tail_norm
end StrictEUnit
