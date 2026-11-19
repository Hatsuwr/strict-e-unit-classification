import BinomialSplittingField
import PowerBasisConductor
import Mathlib.RingTheory.Polynomial.GaussLemma

noncomputable section
open Polynomial IsLocalization
open scoped nonZeroDivisors NumberField
namespace StrictEUnit

/-- Clearing a rational Bezout identity leaves one nonzero integer obstruction. -/
theorem integer_bezout_of_rational_coprime (f g : ℤ[X])
    (h : IsCoprime (f.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ))) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ A B : ℤ[X], A * f + B * g = C d := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨⟨c, hc0⟩, hc⟩ := integerNormalization_map_to_map ℤ⁰ a
  obtain ⟨⟨d, hd0⟩, hd⟩ := integerNormalization_map_to_map ℤ⁰ b
  rw [Algebra.smul_def, Polynomial.algebraMap_apply, Subtype.coe_mk] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at hc0 hd0
  refine ⟨c*d, mul_ne_zero hc0 hd0,
    C d * integerNormalization ℤ⁰ a, C c * integerNormalization ℤ⁰ b, ?_⟩
  apply map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hc, hd, map_mul]
  calc
    _ = C ((algebraMap ℤ ℚ c)*(algebraMap ℤ ℚ d)) * (a * f.map (algebraMap ℤ ℚ) +
      b * g.map (algebraMap ℤ ℚ)) := by rw [map_mul]; ring
    _ = _ := by rw [hab, mul_one]; simp [map_mul]

/-- A rationally separable integer polynomial remains separable modulo
all primes outside an explicit finite set; no prime-distribution hypothesis. -/
theorem separable_reduction_finite_exceptions (f : ℤ[X])
    (hf : (f.map (algebraMap ℤ ℚ)).Separable) :
    ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
      (f.map (Int.castRingHom (ZMod p))).Separable := by
  have hcop : IsCoprime (f.map (algebraMap ℤ ℚ))
      (f.derivative.map (algebraMap ℤ ℚ)) := by
    simpa only [separable_def, derivative_map] using hf
  obtain ⟨d, hd, A, B, hAB⟩ := integer_bezout_of_rational_coprime f f.derivative hcop
  refine ⟨d.natAbs.divisors, ?_⟩
  intro p hp hnot
  letI : Fact p.Prime := ⟨hp⟩
  have hdmod : (d : ZMod p) ≠ 0 := by
    intro hz
    apply hnot
    exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hz),
      Int.natAbs_ne_zero.mpr hd⟩
  let φ := Int.castRingHom (ZMod p)
  have hm := congrArg (Polynomial.map φ) hAB
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C] at hm
  refine ⟨C ((d : ZMod p)⁻¹) * A.map φ, C ((d : ZMod p)⁻¹) * B.map φ, ?_⟩
  rw [derivative_map]
  calc
    _ = C ((d : ZMod p)⁻¹) * (A.map φ * f.map φ + B.map φ * f.derivative.map φ) := by ring
    _ = 1 := by rw [hm, ← map_mul]; simp [φ, hdmod]

/-- Actual integral number-field elements satisfy the rational separability
premise, so the finite exceptional set is constructed unconditionally. -/
theorem integral_minpoly_separable_reduction_finite_exceptions
    {K : Type*} [Field K] [NumberField K] (a : 𝓞 K) :
    ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
      ((minpoly ℤ a).map (Int.castRingHom (ZMod p))).Separable := by
  apply separable_reduction_finite_exceptions
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K
    (NumberField.RingOfIntegers.isIntegral a)]
  exact Algebra.IsSeparable.isSeparable ℚ (algebraMap (𝓞 K) K a)

end StrictEUnit
end
