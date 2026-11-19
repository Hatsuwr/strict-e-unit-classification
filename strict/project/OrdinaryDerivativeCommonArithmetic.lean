import OrdinaryBorelDerivativeArithmetic

/-! NEW SOURCE-ONLY. One original denominator sequence clears all ordinary
 derivatives through r after the single shift N+r. No monotonicity of delta
 is used: its growth comes from the r-fold certificate; integrality uses slack. -/
noncomputable section
namespace StrictEUnit

def ordinaryDerivativeArithmeticConstant (C : ℝ) : ℕ → ℝ
  | 0 => C
  | r + 1 => 2 * (ordinaryDerivativeArithmeticConstant C r)^2

/-- Exact iteration of the accepted certificate, without reselecting witnesses. -/
theorem ordinaryDerivative_iterated_arithmetic_bounds
    (a : ℕ → AlgebraicComplex) (C : ℝ) (hC : 1 ≤ C)
    (hconj : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖σ (a n)‖ ≤ C^(n+1))
    (δ : ℕ → ℕ) (hδ : ∀ N, 0 < δ N)
    (hδbound : ∀ N, (δ N : ℝ) ≤ C^(N+1))
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ N : ℂ) * (a j : ℂ)))
    (r : ℕ) :
    1 ≤ ordinaryDerivativeArithmeticConstant C r ∧
    (∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n,
      ‖σ (((ordinaryDerivativeCoefficients^[r]) a) n)‖ ≤
        (ordinaryDerivativeArithmeticConstant C r)^(n+1)) ∧
    (∀ N, 0 < δ (N+r)) ∧
    (∀ N, (δ (N+r) : ℝ) ≤ (ordinaryDerivativeArithmeticConstant C r)^(N+1)) ∧
    (∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ (N+r) : ℂ) *
      (((ordinaryDerivativeCoefficients (R := AlgebraicComplex)^[r]) a) j : ℂ))) := by
  induction r with
  | zero =>
    simp only [ordinaryDerivativeArithmeticConstant, Function.iterate_zero_apply, Nat.add_zero]
    exact ⟨hC, hconj, hδ, hδbound, hint⟩
  | succ r ih =>
    obtain ⟨hCr, hc, hd, hdb, hi⟩ := ih
    have h := ordinaryDerivativeCoefficients_arithmetic_bounds
      ((ordinaryDerivativeCoefficients^[r]) a) (ordinaryDerivativeArithmeticConstant C r)
      hCr hc (fun N => δ (N+r)) hd hdb hi
    simpa only [ordinaryDerivativeArithmeticConstant, Function.iterate_succ_apply',
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Clearing a longer ORIGINAL prefix clears a lower derivative coefficient.
This is not a divisibility or monotonicity assertion about delta. -/
theorem ordinaryDerivative_integral_slack
    (a : ℕ → AlgebraicComplex) (δ : ℕ → ℕ)
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ N : ℂ) * (a j : ℂ)))
    (k N n : ℕ) (hn : n+k ≤ N) :
    IsIntegral ℤ ((δ N : ℂ) *
      (((ordinaryDerivativeCoefficients (R := AlgebraicComplex)^[k]) a) n : ℂ)) := by
  induction k generalizing n with
  | zero =>
    simpa only [Function.iterate_zero_apply] using hint N n (by omega)
  | succ k ih =>
    have h := (strictE_natCast_isIntegral (n+1)).mul (ih (n+1) (by omega))
    change IsIntegral ℤ ((δ N : ℂ) * (algebraicClosure ℚ ℂ).val
      (((ordinaryDerivativeCoefficients^[k+1]) a) n))
    simp only [Function.iterate_succ_apply', ordinaryDerivativeCoefficients,
      map_mul, map_natCast]
    convert h using 1 <;> ring <;> rfl

/-- The SAME C_r and delta(N+r) work simultaneously for all k<=r. -/
theorem ordinaryDerivative_common_arithmetic_bounds
    (a : ℕ → AlgebraicComplex) (C : ℝ) (hC : 1 ≤ C)
    (hconj : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖σ (a n)‖ ≤ C^(n+1))
    (δ : ℕ → ℕ) (hδ : ∀ N, 0 < δ N)
    (hδbound : ∀ N, (δ N : ℝ) ≤ C^(N+1))
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ N : ℂ) * (a j : ℂ)))
    (r : ℕ) :
    1 ≤ ordinaryDerivativeArithmeticConstant C r ∧
    (∀ k, k ≤ r → ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n,
      ‖σ (((ordinaryDerivativeCoefficients^[k]) a) n)‖ ≤
        (ordinaryDerivativeArithmeticConstant C r)^(n+1)) ∧
    (∀ N, 0 < δ (N+r)) ∧
    (∀ N, (δ (N+r) : ℝ) ≤ (ordinaryDerivativeArithmeticConstant C r)^(N+1)) ∧
    (∀ k, k ≤ r → ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ (N+r) : ℂ) *
      (((ordinaryDerivativeCoefficients (R := AlgebraicComplex)^[k]) a) j : ℂ))) := by
  have hall := ordinaryDerivative_iterated_arithmetic_bounds a C hC hconj δ hδ hδbound hint
  have hmono : Monotone (ordinaryDerivativeArithmeticConstant C) := by
    apply monotone_nat_of_le_succ
    intro k
    have hk := (hall k).1
    change ordinaryDerivativeArithmeticConstant C k ≤
      2 * (ordinaryDerivativeArithmeticConstant C k)^2
    nlinarith
  refine ⟨(hall r).1, ?_, (hall r).2.2.1, (hall r).2.2.2.1, ?_⟩
  · intro k hk σ n
    exact ((hall k).2.1 σ n).trans
      (pow_le_pow_left₀ (zero_le_one.trans (hall k).1) (hmono hk) (n+1))
  · intro k hk N j hj
    exact ordinaryDerivative_integral_slack a δ hint k (N+r) j (by omega)

/-- Ordinary derivative coefficients commute with the actual coefficient map. -/
theorem ordinaryDerivative_iterate_coeff_map {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (a : ℕ → R) (k n : ℕ) :
    f (((ordinaryDerivativeCoefficients^[k]) a) n) =
      ((ordinaryDerivativeCoefficients^[k]) (fun j => f (a j))) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ordinaryDerivativeCoefficients,
      map_mul, map_natCast, ih]

/-- Generic ordinary formal identity, before any number-field specialization. -/
theorem ordinaryDerivative_iterate_mk {R : Type*} [CommSemiring R]
    (a : ℕ → R) (k : ℕ) :
    (PowerSeries.derivative R)^[k] (PowerSeries.mk a) =
      PowerSeries.mk ((ordinaryDerivativeCoefficients^[k]) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, powerSeries_derivative_mk_ordinary]

end StrictEUnit
end
