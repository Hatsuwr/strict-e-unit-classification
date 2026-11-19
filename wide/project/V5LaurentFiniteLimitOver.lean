import V5RankOneRay
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
open scoped Topology
open Filter
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- A finite right limit forces all apparent denominator powers to cancel. -/
theorem v5_polynomial_power_divides_of_finite_limit_over (ι : K →+* ℂ) (N : ℕ) (P : Polynomial K) (d : ℂ)
    (hf : Tendsto (fun x : ℝ => P.eval₂ ι (x : ℂ) / (x : ℂ)^N) (𝓝[>] 0) (𝓝 d)) :
    ∃ Q : Polynomial K, P = Polynomial.X^N * Q := by
  induction N generalizing P with
  | zero => exact ⟨P, by simp⟩
  | succ N ih =>
    have hP0 : P.eval₂ ι 0 = 0 := by
      apply v5_right_limit_excludes_pole (Nat.succ_pos N) hf
      have he : (fun x : ℝ => (x : ℂ)^(N+1) * (P.eval₂ ι (x : ℂ) / (x : ℂ)^(N+1)))
          =ᶠ[𝓝[>] 0] (fun x : ℝ => P.eval₂ ι (x : ℂ)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
        exact mul_div_cancel₀ _ (pow_ne_zero _ hx0)
      exact (((P.continuous_eval₂ ι).comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds).congr' he.symm
    have hdvd : Polynomial.X ∣ P := Polynomial.X_dvd_iff.mpr (by apply ι.injective; simpa only [map_zero, Polynomial.eval₂_at_zero] using hP0)
    obtain ⟨Q, hQ⟩ := hdvd
    have hlim : Tendsto (fun x : ℝ => Q.eval₂ ι (x : ℂ) / (x : ℂ)^N) (𝓝[>] 0) (𝓝 d) := by
      apply hf.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
      rw [hQ, Polynomial.eval₂_mul, Polynomial.eval₂_X, pow_succ]
      field_simp
      ring
    obtain ⟨R, hR⟩ := ih Q hlim
    refine ⟨R, ?_⟩
    rw [hQ, hR, pow_succ]
    ring

def v5RayLaurentEvalOver (ι : K →+* ℂ) (L : LaurentPolynomial K) (x : ℝ) : ℂ :=
  if hx : (x : ℂ) = 0 then 0 else
    LaurentPolynomial.eval₂ ι (Units.mk0 (x : ℂ) hx) L

/-- Finite Laurent evaluation with a finite right limit has no negative powers.
This constructs a polynomial, including zero and positive-order cases. -/
theorem v5_laurent_polynomial_of_finite_right_limit_over (ι : K →+* ℂ) (L : LaurentPolynomial K) (d : ℂ)
    (hL : Tendsto (v5RayLaurentEvalOver ι L) (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    ∃ Q : Polynomial K, L = Polynomial.toLaurent Q ∧ Q.eval₂ ι 0 = d := by
  induction L using LaurentPolynomial.induction_on_mul_T with
  | @Qf P N =>
    have he : v5RayLaurentEvalOver ι (Polynomial.toLaurent P * LaurentPolynomial.T (-(N : ℤ)))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun x : ℝ => P.eval₂ ι (x : ℂ) / (x : ℂ)^N) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
      simp only [v5RayLaurentEvalOver, dif_neg hx0, map_mul,
        LaurentPolynomial.eval₂_toLaurent, LaurentPolynomial.eval₂_T_neg_n,
        Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_mul_inv, inv_pow]
    have hlim := hL.congr' he
    obtain ⟨Q, hQ⟩ := v5_polynomial_power_divides_of_finite_limit_over ι N P d hlim
    have hEq : Polynomial.toLaurent P * LaurentPolynomial.T (-(N : ℤ)) = Polynomial.toLaurent Q := by
      rw [hQ, map_mul, Polynomial.toLaurent_X_pow]
      rw [mul_right_comm, ← LaurentPolynomial.T_add]
      simp
    refine ⟨Q, hEq, ?_⟩
    have hv : (fun x : ℝ => P.eval₂ ι (x : ℂ) / (x : ℂ)^N)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun x : ℝ => Q.eval₂ ι (x : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
      rw [hQ, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact mul_div_cancel_left₀ _ (pow_ne_zero N hx0)
    exact tendsto_nhds_unique
      (((Q.continuous_eval₂ ι).comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hlim.congr' hv)

end StrictEUnit
#print axioms StrictEUnit.v5_polynomial_power_divides_of_finite_limit_over
#print axioms StrictEUnit.v5_laurent_polynomial_of_finite_right_limit_over
