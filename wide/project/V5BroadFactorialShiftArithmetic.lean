import V5BroadAlgebraicDescent
import V5BroadPowerArithmetic

noncomputable section
namespace StrictEUnit

/-- Broad factorial-coefficient arithmetic is stable under every finite shift. -/
theorem v5_broad_algebraicArithmetic_shift
    (a : ℕ → AlgebraicComplex) (ha : V5BroadAlgebraicArithmetic a) (j : ℕ) :
    V5BroadAlgebraicArithmetic (fun n => a (n+j)) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hδb, hab, hi⟩ := ha ε hε
  let F : ℝ := 2^(j*(j+2))
  have hF : 1 ≤ F := by dsimp [F]; exact one_le_pow₀ (by norm_num)
  have hF0 : 0 ≤ F := le_trans (by norm_num) hF
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hFr : 1 ≤ F^ε := Real.one_le_rpow hF (le_of_lt hε)
  let D : ℝ := C^(j+1) * F^ε
  have hD : 1 ≤ D := by
    dsimp only [D]
    nlinarith [one_le_pow₀ hC (n := j+1)]
  have hbound (n : ℕ) :
      C^(n+j+1) * ((n+j).factorial : ℝ)^ε ≤
        D^(n+1) * (n.factorial : ℝ)^ε := by
    have hshift : ((n+j).factorial : ℝ) ≤ F^(n+1) * (n.factorial : ℝ) := by
      dsimp only [F]
      exact_mod_cast v5_factorial_shift_bound n j
    have hCp : C^(n+j+1) ≤ (C^(j+1))^(n+1) := by
      rw [← pow_mul]
      apply pow_le_pow_right₀ hC
      nlinarith
    have hFp : (F^(n+1))^ε = (F^ε)^(n+1) := by
      rw [← Real.rpow_natCast_mul hF0, mul_comm, Real.rpow_mul_natCast hF0]
    calc
      _ ≤ (C^(j+1))^(n+1) * (F^(n+1) * (n.factorial : ℝ))^ε :=
        mul_le_mul hCp (Real.rpow_le_rpow (by positivity) hshift (le_of_lt hε))
          (by positivity) (by positivity)
      _ = D^(n+1) * (n.factorial : ℝ)^ε := by
        rw [Real.mul_rpow (by positivity) (by positivity), hFp]
        dsimp only [D]
        rw [mul_pow]
        ring
  refine ⟨D, hD, (fun L => δ (L+j)), (fun L => hδ (L+j)), ?_, ?_, ?_⟩
  · intro L
    exact (hδb (L+j)).trans (hbound L)
  · intro τ n
    exact (hab τ (n+j)).trans (hbound n)
  · intro L n hn
    exact hi (L+j) (n+j) (Nat.add_le_add_right hn j)

#print axioms v5_broad_algebraicArithmetic_shift
end StrictEUnit
