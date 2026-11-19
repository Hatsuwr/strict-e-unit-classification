import V5WideSolutionDifferential
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace StrictEUnit

/-- Literal Kummer chain rule on the punctured plane, including the natural
exponent zero if the map is constant. -/
theorem V5HasPuncturedDeriv.kummer_pullback {f df : V5PuncturedFunctions}
    (hf : V5HasPuncturedDeriv f df) (q : ℕ) :
    V5HasPuncturedDeriv (fun z => f (z^q))
      (fun z => ((q : ℂ) * (z : ℂ)^(q-1)) * df (z^q)) := by
  obtain ⟨F,hF,hD⟩ := hf
  refine ⟨fun w => F (w^q), ?_, ?_⟩
  · intro z
    simpa only [Units.val_pow_eq_pow_val] using hF (z^q)
  · intro z
    have hDz := hD (z^q)
    have hpow : HasDerivAt (fun w : ℂ => w^q) ((q : ℂ)*(z : ℂ)^(q-1)) (z : ℂ) :=
      hasDerivAt_pow q (z : ℂ)
    rw [Units.val_pow_eq_pow_val] at hDz
    simpa only [mul_comm] using hDz.comp (z : ℂ) hpow

/-- Multiplication by the Kummer coordinate turns the ordinary chain rule
into the exact Euler scaling used by differential descent. -/
theorem v5_punctured_kummer_euler (q : ℕ) (z : ℂˣ) (y : ℂ) :
    (z : ℂ) * (((q : ℂ) * (z : ℂ)^(q-1)) * y) =
      (q : ℂ) * (((z^q : ℂˣ) : ℂ) * y) := by
  cases q with
  | zero => simp
  | succ n =>
    simp only [Units.val_pow_eq_pow_val, Nat.succ_sub_one, pow_succ, Units.val_mul]
    ring

end StrictEUnit
#print axioms StrictEUnit.V5HasPuncturedDeriv.kummer_pullback
#print axioms StrictEUnit.v5_punctured_kummer_euler
