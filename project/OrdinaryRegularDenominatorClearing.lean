import OrdinaryPointPowerSeries
import MinimalDifferentialCompanion
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Ordinary clearing derived from actual power-series preimages.
The reduced denominator cannot vanish at the supplied point. Products of those
same denominators then clear a finite rational family and its literal companion.
No ordinary-clearing premise is added to the scalar regularity hypothesis. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

variable {K : Type*} [Field K]

/-- The reduced numerator supplies the exact denominator-clearing identity. -/
theorem ratFunc_num_eq_denom_mul (q : RatFunc K) :
    algebraMap (Polynomial K) (RatFunc K) q.num =
      algebraMap (Polynomial K) (RatFunc K) q.denom * q := by
  have h := (div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero q))).mp
    (RatFunc.num_div_denom q)
  simpa only [mul_comm] using h

/-- A genuine power-series preimage forces the reduced denominator to avoid
the point. Vanishing of its constant coefficient would force both coprime
polynomials to vanish there, contradicting their Bezout identity. -/
theorem ordinaryPointRationalMap_denom_eval_ne_zero_of_regular
    (α : K) (q : RatFunc K)
    (hreg : ∃ S : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K S = ordinaryPointRationalMap α q) :
    q.denom.eval α ≠ 0 := by
  obtain ⟨S, hS⟩ := hreg
  have hseries : ordinaryPointPolynomialSeries α q.num =
      ordinaryPointPolynomialSeries α q.denom * S := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [map_mul, ordinaryPointPolynomialSeries_coe,
      ordinaryPointPolynomialSeries_coe, hS]
    simpa only [map_mul, ordinaryPointRationalMap_polynomial] using
      congrArg (ordinaryPointRationalMap α) (ratFunc_num_eq_denom_mul q)
  intro hden
  have hnum := congrArg (PowerSeries.constantCoeff K) hseries
  simp only [map_mul, ordinaryPointPolynomialSeries_constantCoeff,
    hden, zero_mul] at hnum
  obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom q
  have heval := congrArg (Polynomial.eval α) hab
  have hzero : (0 : K) = 1 := by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      hnum, hden, mul_zero, add_zero] using heval
  exact zero_ne_one hzero

theorem ordinaryPointRationalMap_regular_iff_denom_eval_ne_zero
    (α : K) (q : RatFunc K) :
    (∃ S : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K S = ordinaryPointRationalMap α q) ↔
      q.denom.eval α ≠ 0 := by
  constructor
  · exact ordinaryPointRationalMap_denom_eval_ne_zero_of_regular α q
  · intro hden
    refine ⟨ordinaryPointPolynomialSeries α q.num *
      (ordinaryPointPolynomialSeries α q.denom)⁻¹, ?_⟩
    exact (ordinaryPointRationalMap_of_clearing α q q.denom q.num hden
      (ratFunc_num_eq_denom_mul q)).symm

/-- One denominator, nonvanishing at the same supplied point, clears an
arbitrary finite family. The empty family is allowed. -/
theorem exists_ordinary_polynomial_family_clearing
    {I : Type*} [Fintype I] (α : K) (q : I → RatFunc K)
    (hreg : ∀ i, ∃ S : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K S = ordinaryPointRationalMap α (q i)) :
    ∃ T : Polynomial K, T.eval α ≠ 0 ∧ ∃ U : I → Polynomial K,
      ∀ i, algebraMap (Polynomial K) (RatFunc K) (U i) =
        algebraMap (Polynomial K) (RatFunc K) T * q i := by
  classical
  have hden (i : I) : (q i).denom.eval α ≠ 0 :=
    ordinaryPointRationalMap_denom_eval_ne_zero_of_regular α (q i) (hreg i)
  let T : Polynomial K := ∏ i, (q i).denom
  let D : I → Polynomial K := fun i =>
    ∏ j ∈ (Finset.univ : Finset I).erase i, (q j).denom
  have hT : T.eval α ≠ 0 := by
    dsimp only [T]
    rw [Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hden i)
  have hD (i : I) : D i * (q i).denom = T := by
    exact Finset.prod_erase_mul Finset.univ (fun j => (q j).denom)
      (Finset.mem_univ i)
  refine ⟨T, hT, (fun i => D i * (q i).num), ?_⟩
  intro i
  rw [map_mul, ratFunc_num_eq_denom_mul, ← mul_assoc, ← map_mul, hD i]

/-- Matrix specialization retains the same exact clearing identity. -/
theorem exists_ordinary_polynomial_matrix_clearing
    {I J : Type*} [Fintype I] [Fintype J]
    (α : K) (A : I → J → RatFunc K)
    (hreg : ∀ i j, ∃ S : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K S = ordinaryPointRationalMap α (A i j)) :
    ∃ T : Polynomial K, T.eval α ≠ 0 ∧ ∃ U : I → J → Polynomial K,
      ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) T * A i j := by
  obtain ⟨T, hT, U, hU⟩ := exists_ordinary_polynomial_family_clearing α
    (fun ij : I × J => A ij.1 ij.2) (fun ij => hreg ij.1 ij.2)
  exact ⟨T, hT, (fun i j => U (i, j)), (fun i j => hU (i, j))⟩

/-- The original scalar regularity hypothesis extends to the literal
companion: its other entries are only zero and one. -/
theorem minimalDerivativeCompanion_ordinary_regular
    (α : K) (r : ℕ) (b : Fin r → RatFunc K)
    (hreg : ∀ j, ∃ S : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K S = ordinaryPointRationalMap α (b j)) :
    ∀ i j, ∃ S : PowerSeries K, HahnSeries.ofPowerSeries ℤ K S =
      ordinaryPointRationalMap α (minimalDerivativeCompanion r b i j) := by
  intro i j
  by_cases hi : i.val + 1 < r
  · by_cases hj : j.val = i.val + 1
    · refine ⟨1, ?_⟩
      simp [minimalDerivativeCompanion, hi, hj]
    · refine ⟨0, ?_⟩
      simp [minimalDerivativeCompanion, hi, hj]
  · simpa only [minimalDerivativeCompanion, if_neg hi] using hreg j

/-- The ordinary denominator for the SAME minimal companion is constructed
from the original scalar power-series-preimage hypotheses, rather than assumed. -/
theorem exists_ordinary_minimal_companion_clearing
    (α : K) (r : ℕ) (b : Fin r → RatFunc K)
    (hreg : ∀ j, ∃ S : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K S = ordinaryPointRationalMap α (b j)) :
    ∃ T : Polynomial K, T.eval α ≠ 0 ∧
      ∃ U : Fin r → Fin r → Polynomial K,
        ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
          algebraMap (Polynomial K) (RatFunc K) T *
            minimalDerivativeCompanion r b i j := by
  exact exists_ordinary_polynomial_matrix_clearing α
    (minimalDerivativeCompanion r b)
    (minimalDerivativeCompanion_ordinary_regular α r b hreg)

end StrictEUnit
end
