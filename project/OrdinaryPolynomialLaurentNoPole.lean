import OrdinaryLaurentNoPole
import OrdinaryPointPowerSeries

/-! A supplied polynomial operator ordinary at the specified point has no
Laurent-pole solutions. The same coefficient tuple is retained, including order zero. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem laurent_powerSeries_polynomial_relation_powerSeries
    {K : Type*} [Field K] [CharZero K] (m : ℕ)
    (p : Fin (m+1) → PowerSeries K)
    (hord : PowerSeries.constantCoeff K (p (Fin.last m)) ≠ 0)
    (u : LaurentSeries K)
    (hrel : (∑ i, HahnSeries.ofPowerSeries ℤ K (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) = 0) :
    ∃ w : PowerSeries K, HahnSeries.ofPowerSeries ℤ K w = u := by
  classical
  let φ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  have hinv : φ ((p (Fin.last m))⁻¹) * φ (p (Fin.last m)) = 1 := by
    rw [← map_mul, PowerSeries.inv_mul_cancel _ hord, map_one]
  by_cases hm : m = 0
  · subst m
    have he : φ (p (Fin.last 0)) * u = 0 := by
      change (∑ i : Fin 1, φ (p i) *
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) = 0 at hrel
      rw [Fin.sum_univ_one] at hrel
      exact hrel
    have hz : u = 0 := by
      calc
        u = (φ ((p (Fin.last 0))⁻¹) * φ (p (Fin.last 0))) * u := by rw [hinv, one_mul]
        _ = 0 := by rw [mul_assoc, he, mul_zero]
    exact ⟨0, by rw [map_zero, hz]⟩
  · let b : Fin m → PowerSeries K := fun i => -p i.castSucc * (p (Fin.last m))⁻¹
    have he : (∑ i : Fin m, φ (p i.castSucc) *
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) =
      -(φ (p (Fin.last m)) *
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[m] u) := by
      rw [Fin.sum_univ_castSucc] at hrel
      exact eq_neg_of_add_eq_zero_left hrel
    apply laurent_ordinary_recurrence_solution_powerSeries m (Nat.pos_of_ne_zero hm) b u
    change (∑ i : Fin m, φ (b i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) = _
    calc
      _ = -φ ((p (Fin.last m))⁻¹) * (∑ i : Fin m, φ (p i.castSucc) *
          (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [b, map_mul, map_neg]
        ring
      _ = _ := by rw [he]; simp only [neg_mul_neg]; rw [← mul_assoc, hinv, one_mul]

theorem ordinaryPoint_polynomial_relation_powerSeries
    {K : Type*} [Field K] [CharZero K] (α : K) (m : ℕ)
    (p : Fin (m+1) → Polynomial K) (hord : (p (Fin.last m)).eval α ≠ 0)
    (u : LaurentSeries K)
    (hrel : (∑ i, ordinaryPointPolynomialMap α (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) = 0) :
    ∃ w : PowerSeries K, HahnSeries.ofPowerSeries ℤ K w = u := by
  apply laurent_powerSeries_polynomial_relation_powerSeries m
    (fun i => ordinaryPointPolynomialSeries α (p i))
    (by simpa only [ordinaryPointPolynomialSeries_constantCoeff] using hord) u
  simpa only [ordinaryPointPolynomialSeries_coe] using hrel

theorem ordinaryPoint_polynomial_relation_coeff_neg
    {K : Type*} [Field K] [CharZero K] (α : K) (m : ℕ)
    (p : Fin (m+1) → Polynomial K) (hord : (p (Fin.last m)).eval α ≠ 0)
    (u : LaurentSeries K)
    (hrel : (∑ i, ordinaryPointPolynomialMap α (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] u) = 0) :
    ∀ n : ℤ, n < 0 → u.coeff n = 0 := by
  obtain ⟨w, hw⟩ := ordinaryPoint_polynomial_relation_powerSeries α m p hord u hrel
  intro n hn
  rw [← hw]
  exact powerSeries_laurent_coeff_neg w n hn
end StrictEUnit
