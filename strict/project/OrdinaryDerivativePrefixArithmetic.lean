import OrdinaryDerivativePrefix
import OrdinaryDerivativeCommonArithmetic
import StrictArithmeticIntegralPrefix

/-! NEW SOURCE-ONLY. The literal Fin r prefix is cleared by the same original
 delta(N+r) and bounded by C_r. No unit branch, monotonicity of delta, or new
 arithmetic premise replaces the accepted common-certificate construction. -/
noncomputable section
open scoped NumberField
namespace StrictEUnit

/-- Integral and house-bounded prefixes for precisely G,...,D^(r-1)G.
The harmless extra derivative in C_r/delta(N+r) is only a common bound. -/
theorem strictE_derivative_prefix_integral_house
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F)
    (C : ℝ) (hC : 1 ≤ C)
    (hconj : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖σ (a n)‖ ≤ C^(n+1))
    (δ : ℕ → ℕ) (hδ : ∀ N, 0 < δ N)
    (hδbound : ∀ N, (δ N : ℝ) ≤ C^(N+1))
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((δ N : ℂ) * (a j : ℂ)))
    (r : ℕ) :
    1 ≤ ordinaryDerivativeArithmeticConstant C r ∧
    (∀ i N n, n ≤ N → IsIntegral ℤ ((δ (N+r) : F) * PowerSeries.coeff F n
      (ordinaryDerivativePrefix r (PowerSeries.mk (strictEFieldCoefficient F a hmem)) i))) ∧
    (∀ i N n, n ≤ N → NumberField.house ((δ (N+r) : F) * PowerSeries.coeff F n
      (ordinaryDerivativePrefix r (PowerSeries.mk (strictEFieldCoefficient F a hmem)) i)) ≤
        (ordinaryDerivativeArithmeticConstant C r)^(2*(N+1))) := by
  have ha : HasStrictEArithmetic a := ⟨C, hC, hconj, δ, hδ, hδbound, hint⟩
  obtain ⟨hCr, hconjr, _hδr, hδboundr, hintr⟩ :=
    ordinaryDerivative_common_arithmetic_bounds a C hC hconj δ hδ hδbound hint r
  let α := strictEFieldCoefficient F a hmem
  let b : Fin r → ℕ → AlgebraicComplex := fun k => (ordinaryDerivativeCoefficients^[k.val]) a
  have hbmem (k : Fin r) : ∀ n, b k n ∈ F :=
    (strictEArithmetic_iterate_ordinaryDerivative ha k.val).2.2 F hmem
  have hcoeff (k : Fin r) (n : ℕ) :
      PowerSeries.coeff F n (ordinaryDerivativePrefix r (PowerSeries.mk α) k) =
        strictEFieldCoefficient F (b k) (hbmem k) n := by
    change PowerSeries.coeff F n
      ((PowerSeries.derivative F)^[k.val] (PowerSeries.mk α)) = _
    rw [ordinaryDerivative_iterate_mk, PowerSeries.coeff_mk]
    apply Subtype.ext
    exact (ordinaryDerivative_iterate_coeff_map F.val.toRingHom α k.val n).trans (by rfl)
  refine ⟨hCr, ?_, ?_⟩
  · intro k N n hn
    rw [hcoeff]
    exact stage44_integral_coefficient_denominator F
      (strictEFieldCoefficient F (b k) (hbmem k))
      (strictEFieldCoefficient_coe F (b k) (hbmem k)) (δ (N+r)) n
      (hintr k.val (Nat.le_of_lt k.isLt) N n hn)
  · intro k N n hn
    rw [hcoeff]
    exact strictEFieldCoefficient_scaled_house_le F (b k) (hbmem k)
      (ordinaryDerivativeArithmeticConstant C r) hCr
      (hconjr k.val (Nat.le_of_lt k.isLt)) (δ (N+r)) N n (hδboundr N) hn

end StrictEUnit
end
