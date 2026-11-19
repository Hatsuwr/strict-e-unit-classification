import MeromorphicOriginRemoval

/-! Exterior growth is unchanged by replacing an arbitrary value at zero.
Removing the actual meromorphic order preserves both bounds via the proved
integer-power bounds, rather than an assumed reciprocal-closure principle. -/
noncomputable section
namespace StrictEUnit

/-- Only values outside the unit disk enter the growth property. -/
theorem powerExponentialBound_congr_exterior {N : ℕ} {f g : ℂ → ℂ}
    (hf : HasPowerExponentialBound N f)
    (hfg : ∀ z, 1 ≤ ‖z‖ → f z = g z) : HasPowerExponentialBound N g := by
  obtain ⟨C, hC, M, h⟩ := hf
  exact ⟨C, hC, M, fun z hz => (hfg z hz) ▸ h z hz⟩

/-- Multiplying by any integral coordinate power preserves the exact bound. -/
theorem powerExponentialBound_zpow_mul {N : ℕ} {v : ℂ → ℂ}
    (q : ℤ) (hv : HasPowerExponentialBound N v) :
    HasPowerExponentialBound N (fun z => z^q * v z) :=
  powerExponentialBound_mul N id _ _ (powerExponentialBound_coordinate_zpow N id q) hv

/-- The normalized global entire function and its actual pointwise inverse
both inherit the exterior bounds of the original punctured function. -/
theorem exists_entire_remove_origin_with_growth {v : ℂ → ℂ} {N : ℕ}
    (hm : MeromorphicAt v 0)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℂ v z)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hv : HasPowerExponentialBound N v)
    (hi : HasPowerExponentialBound N (fun z => (v z)⁻¹)) :
    ∃ q : ℤ, ∃ w : ℂ → ℂ,
      hm.order = (q : WithTop ℤ) ∧ Differentiable ℂ w ∧
      (∀ z, w z ≠ 0) ∧ (∀ z, z ≠ 0 → v z = z^q * w z) ∧
      HasPowerExponentialBound N w ∧
      HasPowerExponentialBound N (fun z => (w z)⁻¹) := by
  obtain ⟨q, w, hq, hwd, hwnz, hw, hvw⟩ := exists_entire_nonzero_remove_origin hm hd hnz
  refine ⟨q, w, hq, hwd, hwnz, hvw, ?_, ?_⟩
  · apply powerExponentialBound_congr_exterior (powerExponentialBound_zpow_mul (-q) hv)
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz)
    exact (hw z hz0).symm
  · apply powerExponentialBound_congr_exterior (powerExponentialBound_zpow_mul q hi)
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz)
    simp only [hw z hz0, mul_inv_rev, zpow_neg, inv_inv, mul_comm]

end StrictEUnit
#print axioms StrictEUnit.powerExponentialBound_congr_exterior
#print axioms StrictEUnit.powerExponentialBound_zpow_mul
#print axioms StrictEUnit.exists_entire_remove_origin_with_growth
