import V5FormalWronskianSpan
import FormalFundamentalMatrixUnit
import OrdinaryPointPowerSeries

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Every Laurent solution of a power-series system is a power series.
The normalized fundamental matrix is constructed, and 087 supplies constants. -/
theorem laurent_ordinary_system_solution_powerSeries
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (u : Fin r → LaurentSeries K)
    (hu : ∀ i, laurentOrdinaryDerivation (u i) =
      ∑ j, HahnSeries.ofPowerSeries ℤ K (A i j) * u j) :
    ∃ w : Fin r → PowerSeries K, ∀ i, HahnSeries.ofPowerSeries ℤ K (w i) = u i := by
  classical
  obtain ⟨W, hW0, hWd, hWu⟩ := exists_normalized_formal_fundamentalMatrix A
  let φ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  let ψ : Matrix (Fin r) (Fin r) (PowerSeries K) →+*
      Matrix (Fin r) (Fin r) (LaurentSeries K) := φ.mapMatrix
  have hdet : (ψ W).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _ |>.mp (hWu.map ψ)).ne_zero
  have hdW : v5LaurentMatrixDerivative (ψ W) = ψ A * ψ W := by
    funext i j
    change laurentOrdinaryDerivation (φ (W i j)) = _
    rw [laurentOrdinaryDerivation_ofPowerSeries]
    have hh := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => φ (M i j)) hWd
    simpa only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul] using hh
  obtain ⟨c,hc⟩ := v5_laurent_solution_vector_span (ψ A) (ψ W) u hdet hdW hu
  refine ⟨fun i => ∑ j, W i j * PowerSeries.C K (c j), ?_⟩
  intro i
  rw [hc i]
  simp only [map_sum, map_mul, HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply]
  rfl

theorem laurent_ordinary_system_solution_coeff_neg
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (u : Fin r → LaurentSeries K)
    (hu : ∀ i, laurentOrdinaryDerivation (u i) =
      ∑ j, HahnSeries.ofPowerSeries ℤ K (A i j) * u j) :
    ∀ i n, n < 0 → (u i).coeff n = 0 := by
  obtain ⟨w, hw⟩ := laurent_ordinary_system_solution_powerSeries A u hu
  intro i n hn
  rw [← hw i]
  exact powerSeries_laurent_coeff_neg (w i) n hn

/-- A normalized ordinary scalar recurrence cannot have a Laurent solution
with a pole. Its companion coefficients are constructed from the recurrence. -/
theorem laurent_ordinary_recurrence_solution_powerSeries
    {K : Type*} [Field K] [CharZero K] (r : ℕ) (hr : 0 < r)
    (b : Fin r → PowerSeries K) (f : LaurentSeries K)
    (hrec : ∑ i, HahnSeries.ofPowerSeries ℤ K (b i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] f =
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[r] f) :
    ∃ w : PowerSeries K, HahnSeries.ofPowerSeries ℤ K w = f := by
  classical
  let A : Matrix (Fin r) (Fin r) (PowerSeries K) := fun i j =>
    if i.val+1<r then (if j.val=i.val+1 then 1 else 0) else b j
  let Y : Fin r → LaurentSeries K := fun i =>
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] f
  have hs : ∀ i, laurentOrdinaryDerivation (Y i) =
      ∑ j, HahnSeries.ofPowerSeries ℤ K (A i j) * Y j := by
    intro i
    change laurentOrdinaryDerivation
      ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] f) = _
    rw [← Function.iterate_succ_apply'
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K) i.val f]
    by_cases hi : i.val+1<r
    · let j0 : Fin r := ⟨i.val+1, hi⟩
      rw [Finset.sum_eq_single j0]
      · simp only [A, if_pos hi, j0, if_true, map_one, one_mul, Y]
      · intro j hj hne
        have hv : j.val ≠ i.val+1 := by
          intro he
          exact hne (Fin.ext he)
        simp only [A, if_pos hi, if_neg hv, map_zero, zero_mul]
      · simp
    · have he : i.val+1=r := by omega
      simpa only [A, if_neg hi, Y, Nat.succ_eq_add_one, he] using hrec.symm
  obtain ⟨w, hw⟩ := laurent_ordinary_system_solution_powerSeries A Y hs
  exact ⟨w ⟨0, hr⟩, hw ⟨0, hr⟩⟩

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

theorem ordinary_scaled_powerSeries_constant_zero
    {K : Type*} [Field K] [CharZero K] (y : PowerSeries K)
    (m : ℕ) (p : Fin (m+1) → PowerSeries K)
    (hord : PowerSeries.constantCoeff K (p (Fin.last m)) ≠ 0)
    (hrel : (∑ i, HahnSeries.ofPowerSeries ℤ K (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        ((HahnSeries.ofPowerSeries ℤ K PowerSeries.X)⁻¹ *
          HahnSeries.ofPowerSeries ℤ K y)) = 0) :
    PowerSeries.constantCoeff K y = 0 := by
  let Φ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  have hx : Φ PowerSeries.X ≠ 0 := by
    intro h
    exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective (h.trans (map_zero Φ).symm))
  obtain ⟨w, hw⟩ := laurent_powerSeries_polynomial_relation_powerSeries m p hord
    ((Φ PowerSeries.X)⁻¹ * Φ y) hrel
  have hpower : PowerSeries.X * w = y := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [map_mul, hw, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  have h := congrArg (PowerSeries.constantCoeff K) hpower
  simpa only [map_mul, PowerSeries.constantCoeff_X, zero_mul] using h.symm

theorem ordinary_scaled_product_exists_constant_zero
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (v : ι → PowerSeries K)
    (m : ℕ) (p : Fin (m+1) → PowerSeries K)
    (hord : PowerSeries.constantCoeff K (p (Fin.last m)) ≠ 0)
    (hrel : (∑ i, HahnSeries.ofPowerSeries ℤ K (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        ((HahnSeries.ofPowerSeries ℤ K PowerSeries.X)⁻¹ *
          HahnSeries.ofPowerSeries ℤ K (∏ j, v j))) = 0) :
    ∃ j, PowerSeries.constantCoeff K (v j) = 0 := by
  have h := ordinary_scaled_powerSeries_constant_zero (∏ j, v j) m p hord hrel
  rw [map_prod] at h
  simpa only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] using h


#print axioms laurent_ordinary_system_solution_powerSeries
#print axioms laurent_ordinary_recurrence_solution_powerSeries
#print axioms laurent_powerSeries_polynomial_relation_powerSeries
#print axioms ordinaryPoint_polynomial_relation_powerSeries
#print axioms ordinary_scaled_powerSeries_constant_zero
#print axioms ordinary_scaled_product_exists_constant_zero
end StrictEUnit
