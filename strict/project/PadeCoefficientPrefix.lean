import Mathlib.RingTheory.PowerSeries.Basic

/-! NEW SOURCE-ONLY R2 partition of ActualTwoChannelPade R1.
Declaration text below is a byte-identical source slice. No elaboration result
is asserted. The original resource stop does not identify a source defect. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- Only coefficients through n of the right factor can affect coefficient n
of a product. This transports finite prefix identities, not entire series. -/
theorem pade_coeff_mul_right_congr {R : Type*} [CommSemiring R]
    (f g h : PowerSeries R) (n : ℕ)
    (heq : ∀ k : ℕ, k ≤ n → PowerSeries.coeff R k g = PowerSeries.coeff R k h) :
    PowerSeries.coeff R n (f * g) = PowerSeries.coeff R n (f * h) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [heq ij.2 (by omega)]


end StrictEUnit
end
