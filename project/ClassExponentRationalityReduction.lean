import GlobalAnalyticLogFrame

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

/-- Natural class shifts cannot remove the external rationality obligation. -/
theorem classExponent_rational_iff
    (rho : Fin r → K) (xi : ExponentClass rho → K) (s : Fin r → ℕ)
    (hs : ∀ j, rho j = xi (exponentClassMap rho j) + (s j : K)) :
    (∀ j, ∃ q : ℚ, rho j = (q : K)) ↔ (∀ c, ∃ q : ℚ, xi c = (q : K)) := by
  constructor
  · intro h c
    obtain ⟨q, hq⟩ := h c.out
    have hc : exponentClassMap rho c.out = c := Quotient.out_eq c
    have he := hs c.out
    rw [hc, hq] at he
    refine ⟨q - (s c.out : ℚ), ?_⟩
    push_cast
    linear_combination -he
  · intro h j
    obtain ⟨q, hq⟩ := h (exponentClassMap rho j)
    refine ⟨q + (s j : ℚ), ?_⟩
    rw [hs, hq]
    push_cast
    rfl

/-- Any successful positive integral ramification already proves rationality;
it cannot be constructed first as a substitute for the missing arithmetic theorem. -/
theorem rational_of_integral_ramification (x : K) (N : ℕ) (hN : 0 < N)
    (m : ℤ) (hm : (N : K) * x = (m : K)) : ∃ q : ℚ, x = (q : K) := by
  refine ⟨(m : ℚ) / (N : ℚ), ?_⟩
  push_cast
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (ne_of_gt hN))).mpr
  simpa only [mul_comm] using hm

end StrictEUnit
end
