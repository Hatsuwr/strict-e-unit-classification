import OrdinaryPolynomialLaurentNoPole
import ActualRationalMinimalSingularity

/-! An ordinary annihilator of t⁻¹ times a power series forces its initial
value to vanish. The actual rational strict-E quotient supplies such an operator. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

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

/-- Actual rational factorial coefficients give the same actual quotient and an
ordinary polynomial annihilator. No minimal recurrence is used in this extraction. -/
theorem rational_actualStrictE_division_ordinary_annihilator
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hfne : f ≠ (fun _ => 0))
    (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z))
    (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsStrictEFunction g ∧
      (∀ z : ℂ, (z - 1) * g z = f z) ∧
      ∃ m : ℕ, ∃ p : Fin (m+1) → Polynomial AlgebraicComplex,
        (p (Fin.last m)).eval 1 ≠ 0 ∧
        ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).toSubfield.subtype z *
          iteratedDeriv i.val g z = 0 := by
  obtain ⟨g, hg, hmul⟩ := strictEFunction_divAtOne_of_rational_representation hf a hrat hs hz
  have hgne : g ≠ (fun _ => 0) := by
    intro hg0
    apply hfne
    funext z
    simpa only [hg0, mul_zero] using (hmul z).symm
  obtain ⟨m, s, c, p, hode, _⟩ := actualStrictE_scalarNormalFormAvailability g hg hgne
  have hord : (p (Fin.last m)).eval 1 ≠ 0 := by
    rw [hode.leading, Polynomial.eval_monomial, one_pow, mul_one]
    exact hode.coefficient_ne_zero
  exact ⟨g, hg, hmul, m, p, hord, hode.equation⟩

end StrictEUnit
