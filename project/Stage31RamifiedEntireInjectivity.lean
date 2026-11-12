import Stage17RamifiedLaurentCoefficients
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Injectivity of actual ramified Taylor realization

Positive complex power maps are surjective. Therefore composing actual entire
functions with a positive power is injective. Composing this proved injection
with the genuine Taylor embedding gives injectivity of the actual ramified
realization. No arbitrary formal series is evaluated as an analytic function.
-/
noncomputable section
namespace StrictEUnit

/-- Actual entire functions are recovered from their positive power pullback,
using existence of complex roots rather than a formal evaluation map. -/
theorem stage31_entirePowerPullback_injective (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (stage17_entirePowerPullback N) := by
  intro f g h
  apply Subtype.ext
  funext z
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (Nat.pos_of_ne_zero hN)
  have hv := congrArg (fun u : entireFunctionAlgebra => u.val w) h
  simpa only [stage17_entirePowerPullback_apply, hw] using hv

/-- Restriction to the actual arithmetic entire-function algebra remains
injective; arithmetic membership is already proved by Stage 17. -/
theorem stage31_arithmeticPowerPullback_injective (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (stage17_arithmeticPowerPullback k N hN) := by
  intro f g h
  apply Subtype.ext
  apply stage31_entirePowerPullback_injective N hN
  exact congrArg Subtype.val h

/-- The literal ramified arithmetic-entire Taylor realization is injective. -/
theorem stage31_ramifiedEntireFormalAlgHom_injective (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (stage17_ramifiedEntireFormalAlgHom k N hN) :=
  (stage17_entireFormalAlgHom_injective k).comp
    (stage31_arithmeticPowerPullback_injective k N hN)

end StrictEUnit
