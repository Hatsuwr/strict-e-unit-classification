import Mathlib.RingTheory.PowerSeries.Derivative

/-! NEW SOURCE-ONLY. Literal ordinary derivative prefix and its polynomial row.
No unit channel or derivative of order r is appended. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

def ordinaryDerivativePrefix {K : Type*} [CommSemiring K] (r : ℕ)
    (G : PowerSeries K) : Fin r → PowerSeries K :=
  fun i => (PowerSeries.derivative K)^[i.val] G

def ordinaryDerivativePrefixRemainder {K : Type*} [CommSemiring K] (r : ℕ)
    (G : PowerSeries K) (P : Fin r → Polynomial K) : PowerSeries K :=
  ∑ i, (P i : PowerSeries K) * ordinaryDerivativePrefix r G i

end StrictEUnit
end
