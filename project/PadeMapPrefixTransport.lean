import PadeCoefficientPrefix
import Mathlib.Algebra.BigOperators.Fin

/-! NEW SOURCE-ONLY, UNCOMPILED. Coefficient-local transport under a ring map
and cancellation of one nonzero scalar, proved over abstract coefficient types.
This module has no IntermediateField, arithmetic, House, or Siegel dependency.
Only finite-prefix coefficient equality is assumed, not a global series identity. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- Map a finite polynomial approximation through φ, replace the right factors
only through the required coefficient range, and cancel the same nonzero δ. -/
theorem pade_map_prefix_cancel {R K ι : Type*}
    [CommSemiring R] [Field K] [Fintype ι]
    (φ : R →+* K) (Q : ι → Polynomial R) (b : ι → ℕ → R)
    (U : ι → PowerSeries K) (δ : K) (hδ : δ ≠ 0) (s : ℕ)
    (hchannel : ∀ i k, k < s → φ (b i k) = δ * PowerSeries.coeff K k (U i))
    (hvan : ∀ n : ℕ, n < s → PowerSeries.coeff R n
      (∑ i, (Q i : PowerSeries R) * PowerSeries.mk (b i)) = 0) :
    ∀ n : ℕ, n < s → PowerSeries.coeff K n
      (∑ i, ((Q i).map φ : PowerSeries K) * U i) = 0 := by
  intro n hn
  have hm : PowerSeries.coeff K n
      (PowerSeries.map φ (∑ i, (Q i : PowerSeries R) * PowerSeries.mk (b i))) = 0 := by
    rw [PowerSeries.coeff_map, hvan n hn, map_zero]
  have hmap : PowerSeries.map φ
      (∑ i, (Q i : PowerSeries R) * PowerSeries.mk (b i)) =
      ∑ i, ((Q i).map φ : PowerSeries K) * PowerSeries.map φ (PowerSeries.mk (b i)) := by
    simp only [map_sum, map_mul, Polynomial.polynomial_map_coe]
  rw [hmap] at hm
  have hterm (i : ι) : PowerSeries.coeff K n
      (((Q i).map φ : PowerSeries K) * PowerSeries.map φ (PowerSeries.mk (b i))) =
      δ * PowerSeries.coeff K n (((Q i).map φ : PowerSeries K) * U i) := by
    calc
      _ = PowerSeries.coeff K n
          (((Q i).map φ : PowerSeries K) * (PowerSeries.C K δ * U i)) := by
        apply pade_coeff_mul_right_congr
        intro k hk
        rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
        exact hchannel i k (lt_of_le_of_lt hk hn)
      _ = _ := by
        rw [show ((Q i).map φ : PowerSeries K) * (PowerSeries.C K δ * U i) =
            PowerSeries.C K δ * (((Q i).map φ : PowerSeries K) * U i) from
          mul_left_comm ((Q i).map φ : PowerSeries K) (PowerSeries.C K δ) (U i),
          PowerSeries.coeff_C_mul]
  have hscaled : δ * PowerSeries.coeff K n
      (∑ i, ((Q i).map φ : PowerSeries K) * U i) = 0 := by
    rw [map_sum, Finset.mul_sum]
    calc
      _ = ∑ i, PowerSeries.coeff K n
          (((Q i).map φ : PowerSeries K) * PowerSeries.map φ (PowerSeries.mk (b i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hterm i).symm
      _ = 0 := by simpa only [map_sum] using hm
  exact mul_left_cancel₀ (M₀ := K) (a := δ)
    (b := PowerSeries.coeff K n (∑ i, ((Q i).map φ : PowerSeries K) * U i))
    (c := (0 : K)) hδ (hscaled.trans (mul_zero δ).symm)

/-- The two-channel specialization performs finite-sum reduction over abstract
K as well, so callers get the literal P₀ + P₁ * mk alpha expression directly. -/
theorem pade_map_two_channel_prefix_cancel {R K : Type*}
    [CommSemiring R] [Field K]
    (φ : R →+* K) (Q : Fin 2 → Polynomial R) (b : Fin 2 → ℕ → R)
    (α : ℕ → K) (δ : K) (hδ : δ ≠ 0) (s : ℕ)
    (hchannel : ∀ i k, k < s → φ (b i k) = δ * PowerSeries.coeff K k
      (if i = 0 then 1 else PowerSeries.mk α))
    (hvan : ∀ n : ℕ, n < s → PowerSeries.coeff R n
      (∑ i, (Q i : PowerSeries R) * PowerSeries.mk (b i)) = 0) :
    ∀ n : ℕ, n < s → PowerSeries.coeff K n
      (((Q 0).map φ : PowerSeries K) + ((Q 1).map φ : PowerSeries K) *
        PowerSeries.mk α) = 0 := by
  let U : Fin 2 → PowerSeries K := fun i => if i = 0 then 1 else PowerSeries.mk α
  have h := pade_map_prefix_cancel φ Q b U δ hδ s hchannel hvan
  intro n hn
  simpa only [Fin.sum_univ_two, U, if_pos rfl,
    if_neg (by decide : (1 : Fin 2) ≠ 0), if_true, mul_one] using h n hn

end StrictEUnit
end
