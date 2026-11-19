import StrictEArithmeticClosure
import Mathlib.RingTheory.PowerSeries.Derivative

/-! NEW SOURCE-ONLY, UNCOMPILED. Arithmetic of the ORIGINAL ordinary derivative
coefficients (n+1)*a(n+1), not the shifted factorial-series coefficients a(n+1).
A supplied arithmetic certificate is transported explicitly using C' = 2*C^2
and delta'_N = delta_(N+1). All embeddings and prefix integrality are retained.
Iterates stay in the SAME supplied intermediate field. No ODE, minimal-operator,
regularity, continuation, or arithmetic local-basis conclusion is asserted. -/
noncomputable section
namespace StrictEUnit

/-- The literal coefficient operation for ordinary formal differentiation. -/
def ordinaryDerivativeCoefficients {R : Type*} [CommSemiring R]
    (a : ℕ → R) (n : ℕ) : R :=
  ((n + 1 : ℕ) : R) * a (n + 1)

/-- Transport all parts of the supplied arithmetic witness explicitly.
The common denominator is shifted, not replaced by a product certificate. -/
theorem ordinaryDerivativeCoefficients_arithmetic_bounds
    (a : ℕ → AlgebraicComplex) (C : ℝ) (hC : 1 ≤ C)
    (hconj : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖σ (a n)‖ ≤ C^(n + 1))
    (δ : ℕ → ℕ) (hδ : ∀ N, 0 < δ N)
    (hδbound : ∀ N, (δ N : ℝ) ≤ C^(N + 1))
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ N : ℂ) * (a j : ℂ))) :
    1 ≤ 2 * C^2 ∧
    (∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n,
      ‖σ (ordinaryDerivativeCoefficients a n)‖ ≤ (2 * C^2)^(n + 1)) ∧
    (∀ N, 0 < δ (N + 1)) ∧
    (∀ N, (δ (N + 1) : ℝ) ≤ (2 * C^2)^(N + 1)) ∧
    (∀ N j : ℕ, j ≤ N → IsIntegral ℤ
      ((δ (N + 1) : ℂ) * (ordinaryDerivativeCoefficients (R := AlgebraicComplex) a j : ℂ))) := by
  have hshift (n : ℕ) : C^(n + 1 + 1) ≤ (C^2)^(n + 1) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hC
    omega
  have hbase : C^2 ≤ 2 * C^2 :=
    le_mul_of_one_le_left (sq_nonneg C) (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hC),
    ?_, (fun N => hδ (N + 1)), ?_, ?_⟩
  · intro σ n
    rw [ordinaryDerivativeCoefficients, map_mul, map_natCast, norm_mul,
      Complex.norm_natCast]
    have hn : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ)^(n + 1) := by
      exact_mod_cast (Nat.le_of_lt (n + 1).lt_two_pow_self)
    calc
      ((n + 1 : ℕ) : ℝ) * ‖σ (a (n + 1))‖ ≤
          (2 : ℝ)^(n + 1) * (C^2)^(n + 1) :=
        mul_le_mul hn ((hconj σ (n + 1)).trans (hshift n))
          (norm_nonneg _) (by positivity)
      _ = (2 * C^2)^(n + 1) := (mul_pow 2 (C^2) (n + 1)).symm
  · intro N
    exact ((hδbound (N + 1)).trans (hshift N)).trans
      (pow_le_pow_left₀ (sq_nonneg C) hbase (N + 1))
  · intro N j hj
    have h := (strictE_natCast_isIntegral (j + 1)).mul
      (hint (N + 1) (j + 1) (Nat.add_le_add_right hj 1))
    change IsIntegral ℤ ((δ (N + 1) : ℂ) *
      (algebraicClosure ℚ ℂ).val (ordinaryDerivativeCoefficients a j))
    simp only [ordinaryDerivativeCoefficients, map_mul, map_natCast]
    convert h using 1 <;> ring <;> rfl

/-- Full strict arithmetic is closed under the ORDINARY derivative operation. -/
theorem strictEArithmetic_ordinaryDerivative {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    HasStrictEArithmetic (ordinaryDerivativeCoefficients a) := by
  obtain ⟨C, hC, hconj, δ, hδ, hδbound, hint⟩ := ha
  obtain ⟨hC', hconj', hδ', hδbound', hint'⟩ :=
    ordinaryDerivativeCoefficients_arithmetic_bounds a C hC hconj δ hδ hδbound hint
  exact ⟨2 * C^2, hC', hconj', (fun N => δ (N + 1)), hδ', hδbound', hint'⟩

/-- The formal identity uses ordinary, not factorial-normalized, coefficients. -/
theorem powerSeries_derivative_mk_ordinary {R : Type*} [CommSemiring R]
    (a : ℕ → R) :
    PowerSeries.derivative R (PowerSeries.mk a) =
      PowerSeries.mk (ordinaryDerivativeCoefficients a) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    ordinaryDerivativeCoefficients, Nat.cast_add, Nat.cast_one]
  exact mul_comm _ _

/-- Every ordinary derivative iterate retains full arithmetic and the literal
formal-series identity. Its coefficients remain in each SAME field containing
the original a, without assuming that field finite or selecting a new field. -/
theorem strictEArithmetic_iterate_ordinaryDerivative
    {a : ℕ → AlgebraicComplex} (ha : HasStrictEArithmetic a) (r : ℕ) :
    HasStrictEArithmetic ((ordinaryDerivativeCoefficients^[r]) a) ∧
    (PowerSeries.derivative AlgebraicComplex)^[r] (PowerSeries.mk a) =
      PowerSeries.mk ((ordinaryDerivativeCoefficients^[r]) a) ∧
    (∀ F : IntermediateField ℚ AlgebraicComplex, (∀ n, a n ∈ F) →
      ∀ n, ((ordinaryDerivativeCoefficients^[r]) a) n ∈ F) := by
  induction r with
  | zero => exact ⟨ha, rfl, fun F hmem => hmem⟩
  | succ r ih =>
    simp only [Function.iterate_succ_apply']
    refine ⟨strictEArithmetic_ordinaryDerivative ih.1, ?_, ?_⟩
    · rw [ih.2.1, powerSeries_derivative_mk_ordinary]
    · intro F hmem n
      change ((n + 1 : ℕ) : AlgebraicComplex) *
        ((ordinaryDerivativeCoefficients^[r]) a) (n + 1) ∈ F
      exact F.mul_mem (F.natCast_mem (n + 1)) (ih.2.2 F hmem (n + 1))

end StrictEUnit
end
