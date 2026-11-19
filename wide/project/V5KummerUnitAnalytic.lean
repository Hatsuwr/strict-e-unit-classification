import V5ActualKummerFunctions
import V5FinitePoleNormalization

noncomputable section
namespace StrictEUnit

/-- A unit in the punctured meromorphic ring is a monomial times an entire
nowhere-zero function; its value at the mark is that entire factor's value. -/
theorem v5_meromorphic_unit_normalization {k : Type*} [CommRing k] [Algebra k ℂ]
    (u : v5MeromorphicZeroAlgebra k) (hu : IsUnit u) :
    ∃ (m : ℤ) (W : ℂ → ℂ), Differentiable ℂ W ∧ (∀ z, W z ≠ 0) ∧
      (∀ z : ℂˣ, u.val z = (z : ℂ)^m * W z) ∧ u.val 1 = W 1 := by
  obtain ⟨n,F,hF,hrep⟩ := u.property
  obtain ⟨a,rfl⟩ := hu
  let v (z : ℂ) : ℂ := if hz : z = 0 then 0 else a.val.val (Units.mk0 z hz)
  let w (z : ℂ) : ℂ := if hz : z = 0 then 0 else a.inv.val (Units.mk0 z hz)
  have hrepr (z : ℂ) (hz : z ≠ 0) : F z = z^n * v z := by
    simpa only [v,dif_neg hz,Units.val_mk0] using hrep (Units.mk0 z hz)
  have huvw (z : ℂ) (hz : z ≠ 0) : v z * w z = 1 := by
    simpa only [v,w,dif_neg hz] using
      congrArg (fun f : v5MeromorphicZeroAlgebra k => f.val (Units.mk0 z hz)) a.val_inv
  obtain ⟨m,W,hW,hWnz,hf,_,_⟩ := v5_finite_pole_inverse_pair_normalization n hF hrepr huvw
  have hf' (z : ℂˣ) : a.val.val z = (z : ℂ)^m * W z := by
    have hz := Units.ne_zero z
    simpa only [v,dif_neg hz,Units.mk0_val] using hf z hz
  exact ⟨m,W,hW,hWnz,hf',by simpa only [Units.val_one,one_zpow,one_mul] using hf' 1⟩

end StrictEUnit
#print axioms StrictEUnit.v5_meromorphic_unit_normalization
