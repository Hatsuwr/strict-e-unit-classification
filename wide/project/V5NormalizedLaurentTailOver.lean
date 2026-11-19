import V5NormalizedRankOne
import V5LaurentFiniteLimitOver

noncomputable section
open scoped Topology
open Filter
namespace StrictEUnit

/-- The actual normalized Euler equation has constant residue m and no
negative Laurent tail. Polynomial primitive construction is a separate step. -/
theorem v5_normalized_laurent_euler_tail_over {K : Type*} [Field K] (ι : K →+* ℂ) (u W b : ℂ → ℂ) (m : ℤ)
    (hW : Differentiable ℂ W) (hW0 : W 0 ≠ 0)
    (hu : ∀ z ≠ 0, HasDerivAt u (b z * u z / z) z)
    (he : ∀ z ≠ 0, u z = z^m * W z)
    (L : LaurentPolynomial K)
    (hL : ∀ z (hz : z ≠ 0), b z = LaurentPolynomial.eval₂ ι (Units.mk0 z hz) L) :
    ∃ Q : Polynomial K,
      L = Polynomial.toLaurent (Polynomial.C (m : K) + Polynomial.X * Q) := by
  have hb := v5_normalized_euler_coefficient_limit u W b m hW hW0 hu he
  have hlim : Tendsto (v5RayLaurentEvalOver ι L) (𝓝[>] (0 : ℝ)) (𝓝 (m : ℂ)) := by
    apply hb.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
    simp only [v5RayLaurentEvalOver, dif_neg hx0]
    exact hL x hx0
  obtain ⟨P, hP, hp0⟩ := v5_laurent_polynomial_of_finite_right_limit_over ι L (m : ℂ) hlim
  have hp0k : P.eval 0 = (m : K) := by
    apply ι.injective
    simpa only [Polynomial.eval₂_at_zero, ← Polynomial.coeff_zero_eq_eval_zero, map_intCast] using hp0
  have hd : Polynomial.X ∣ P - Polynomial.C (m : K) := by
    apply Polynomial.X_dvd_iff.mpr
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub, Polynomial.eval_C, hp0k, sub_self]
  obtain ⟨Q, hQ⟩ := hd
  refine ⟨Q, ?_⟩
  rw [hP]
  congr 1
  exact (sub_eq_iff_eq_add.mp hQ).trans (add_comm _ _)

end StrictEUnit
#print axioms StrictEUnit.v5_normalized_laurent_euler_tail_over
