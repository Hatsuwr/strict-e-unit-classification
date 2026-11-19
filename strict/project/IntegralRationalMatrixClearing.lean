import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.Lifts

/-! NEW SOURCE-ONLY. Clear a finite rational matrix by one polynomial and then
scale BOTH denominator and numerator matrix by ONE nonzero integer. This is
finite coefficient integrality, not an exponential denominator estimate.
No value-at-zero, unit, monicity, regularity or rank condition is asserted. -/
noncomputable section
open scoped Classical NumberField
namespace StrictEUnit

/-- A single nonzero polynomial clears an arbitrary finite rational matrix,
including a zero matrix and the empty index type. -/
theorem exists_polynomial_matrix_clearing (K : Type*) [Field K] (r : ℕ)
    (A : Fin r → Fin r → RatFunc K) :
    ∃ T : Polynomial K, T ≠ 0 ∧ ∃ U : Fin r → Fin r → Polynomial K,
      ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) T * A i j := by
  obtain ⟨T, hT⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun ij : Fin r × Fin r => A ij.1 ij.2)
  choose U hU using hT
  refine ⟨(T : Polynomial K), mem_nonZeroDivisors_iff_ne_zero.mp T.property,
    (fun i j => U (i,j)), ?_⟩
  intro i j
  simpa only [Algebra.smul_def] using hU (i,j)

/-- Every finite family of number-field polynomials can be lifted integrally
by a SINGLE nonzero integer. The conclusion records that exact common scalar. -/
theorem exists_integer_polynomial_family_lift
    (K : Type*) [Field K] [NumberField K] {I : Type*} [Fintype I]
    (p : I → Polynomial K) :
    ∃ z : ℤ, z ≠ 0 ∧ ∃ P : I → Polynomial (𝓞 K),
      ∀ i, (P i).map (algebraMap (𝓞 K) K) = Polynomial.C (z : K) * p i := by
  classical
  letI : Algebra.IsAlgebraic ℤ K :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).mpr
      (NumberField.isAlgebraic K)
  let s : Finset K := Finset.univ.biUnion (fun i => (p i).coeffs)
  obtain ⟨z, hz, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  have hcoeff (i : I) (n : ℕ) : IsIntegral ℤ ((z : K) * (p i).coeff n) := by
    by_cases hn : (p i).coeff n = 0
    · simpa only [hn, mul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : K))
    · have hmem : (p i).coeff n ∈ s :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Polynomial.coeff_mem_coeffs _ _ hn⟩
      have h := hi ((p i).coeff n) hmem
      rw [Algebra.smul_def] at h
      exact h
  have hlift (i : I) : ∃ P : Polynomial (𝓞 K),
      P.map (algebraMap (𝓞 K) K) = Polynomial.C (z : K) * p i := by
    apply (Polynomial.mem_lifts _).mp
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro n
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨(z : K) * (p i).coeff n, hcoeff i n⟩, rfl⟩
  choose P hP using hlift
  exact ⟨z, hz, P, hP⟩

/-- Coherent integral clearing of the SAME A. Both T and U are multiplied by
exactly C(z), not independently rescaled, and the mapped T remains nonzero. -/
theorem exists_integral_polynomial_matrix_clearing
    (K : Type*) [Field K] [NumberField K] (r : ℕ)
    (A : Fin r → Fin r → RatFunc K) :
    ∃ T0 : Polynomial K, T0 ≠ 0 ∧ ∃ U0 : Fin r → Fin r → Polynomial K,
      (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U0 i j) =
        algebraMap (Polynomial K) (RatFunc K) T0 * A i j) ∧
      ∃ z : ℤ, z ≠ 0 ∧ ∃ T : Polynomial (𝓞 K),
      ∃ U : Fin r → Fin r → Polynomial (𝓞 K),
        T.map (algebraMap (𝓞 K) K) = Polynomial.C (z : K) * T0 ∧
        (∀ i j, (U i j).map (algebraMap (𝓞 K) K) = Polynomial.C (z : K) * U0 i j) ∧
        T ≠ 0 ∧ T.map (algebraMap (𝓞 K) K) ≠ 0 ∧
        (∀ i j, algebraMap (Polynomial K) (RatFunc K)
          ((U i j).map (algebraMap (𝓞 K) K)) =
          algebraMap (Polynomial K) (RatFunc K)
            (T.map (algebraMap (𝓞 K) K)) * A i j) := by
  obtain ⟨T0, hT0, U0, hclear⟩ := exists_polynomial_matrix_clearing K r A
  let p : Option (Fin r × Fin r) → Polynomial K := fun o =>
    match o with
    | none => T0
    | some ij => U0 ij.1 ij.2
  obtain ⟨z, hz, P, hP⟩ := exists_integer_polynomial_family_lift K p
  have hzK : (z : K) ≠ 0 := Int.cast_ne_zero.mpr hz
  have hscaled : Polynomial.C (z : K) * T0 ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hzK) hT0
  have hmapne : (P none).map (algebraMap (𝓞 K) K) ≠ 0 := by
    rw [hP none]
    exact hscaled
  have hPne : P none ≠ 0 := by
    intro h
    apply hmapne
    rw [h, Polynomial.map_zero]
  refine ⟨T0, hT0, U0, hclear, z, hz, P none,
    (fun i j => P (some (i,j))), hP none, (fun i j => hP (some (i,j))),
    hPne, hmapne, ?_⟩
  intro i j
  rw [hP (some (i,j)), hP none]
  simp only [p, map_mul, hclear, mul_assoc]

end StrictEUnit
end
