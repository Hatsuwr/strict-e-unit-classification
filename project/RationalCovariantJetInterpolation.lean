import OrdinaryCovariantJetInterpolation
import OrdinaryPointPowerSeries
import RationalCovariantRow

/-! Transport the constructed polynomial covariant jets to the original
rational system at any specified ordinary point, without changing that point
or its given denominator. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] {r : ℕ}

theorem rationalCovariantRow_local_series_iterate (α : K)
    (A : Fin r → Fin r → RatFunc K) (M : Fin r → Fin r → PowerSeries K)
    (hA : ∀ i j, HahnSeries.ofPowerSeries ℤ K (M i j) = ordinaryPointRationalMap α (A i j))
    (q : Fin r → RatFunc K) (v : Fin r → PowerSeries K)
    (hq : ∀ j, HahnSeries.ofPowerSeries ℤ K (v j) = ordinaryPointRationalMap α (q j))
    (n : ℕ) : ∀ j,
    HahnSeries.ofPowerSeries ℤ K ((ordinaryCovariantRow M)^[n] v j) =
      ordinaryPointRationalMap α
        ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[n] q j) := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    intro j
    simp only [Function.iterate_succ_apply', ordinaryCovariantRow, rationalCovariantRow,
      map_add, map_sum, map_mul]
    rw [← laurentOrdinaryDerivation_ofPowerSeries, ih,
      ordinaryPointRationalMap_derivative]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih, hA]

/-- Actual polynomial rows realize arbitrary finite covariant jets at the SAME
ordinary point of the SAME rational system. Values are Laurent constant
coefficients of the proved regular translated iterates. -/
theorem exists_polynomial_rational_covariant_jets [CharZero K]
    (α : K) (A : Fin r → Fin r → RatFunc K)
    (t : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (v : ℕ → Fin r → K) (n : ℕ) :
    ∃ p : Fin r → Polynomial K, ∀ i, i < n → ∀ j,
      (ordinaryPointRationalMap α
        ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[i]
          (fun j => algebraMap (Polynomial K) (RatFunc K) (p j)) j)).coeff 0 = v i j := by
  let M : Fin r → Fin r → PowerSeries K := fun i j =>
    ordinaryPointPolynomialSeries α (U i j) * (ordinaryPointPolynomialSeries α t)⁻¹
  have hM (i j : Fin r) : HahnSeries.ofPowerSeries ℤ K (M i j) =
      ordinaryPointRationalMap α (A i j) :=
    (ordinaryPointRationalMap_of_clearing α (A i j) t (U i j) hα (hclear i j)).symm
  obtain ⟨p, hp⟩ := exists_polynomial_covariant_jets M v n
  let q : Fin r → Polynomial K := fun j => (ordinaryPointPolynomialShift α).symm (p j)
  have hq (j : Fin r) : HahnSeries.ofPowerSeries ℤ K (p j : PowerSeries K) =
      ordinaryPointRationalMap α (algebraMap (Polynomial K) (RatFunc K) (q j)) := by
    rw [ordinaryPointRationalMap_polynomial, ordinaryPointPolynomialMap_apply]
    dsimp only [q]
    rw [AlgEquiv.apply_symm_apply]
    exact (Polynomial.algebraMap_hahnSeries_apply (Γ := ℤ) (p j)).symm
  refine ⟨q, fun i hi j => ?_⟩
  rw [← rationalCovariantRow_local_series_iterate α A M hM _ _ hq i j]
  change (HahnSeries.ofPowerSeries ℤ K
    ((ordinaryCovariantRow M)^[i] (fun j => (p j : PowerSeries K)) j)).coeff (0 : ℕ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  exact hp i hi j
/-- The constructed row keeps the requested initial value literally. -/
theorem exists_polynomial_rational_covariant_jets_with_value [CharZero K]
    (α : K) (A : Fin r → Fin r → RatFunc K)
    (t : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (v : ℕ → Fin r → K) (n : ℕ) (hn : 0 < n) :
    ∃ p : Fin r → Polynomial K,
      (∀ j, (p j).eval α = v 0 j) ∧
      ∀ i, i < n → ∀ j,
        (ordinaryPointRationalMap α
          ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[i]
            (fun j => algebraMap (Polynomial K) (RatFunc K) (p j)) j)).coeff 0 = v i j := by
  obtain ⟨p, hp⟩ := exists_polynomial_rational_covariant_jets α A t U hα hclear v n
  refine ⟨p, ?_, hp⟩
  intro j
  have h0 := hp 0 hn j
  simp only [Function.iterate_zero_apply, ordinaryPointRationalMap_polynomial] at h0
  calc
    (p j).eval α = PowerSeries.constantCoeff K (ordinaryPointPolynomialSeries α (p j)) :=
      (ordinaryPointPolynomialSeries_constantCoeff α (p j)).symm
    _ = (ordinaryPointPolynomialMap α (p j)).coeff 0 := by
      rw [← ordinaryPointPolynomialSeries_coe]
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff, Nat.cast_zero] using
        (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ)
          (ordinaryPointPolynomialSeries α (p j)) 0).symm
    _ = v 0 j := h0
end StrictEUnit

