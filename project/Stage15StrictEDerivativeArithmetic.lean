import StrictEArithmeticSeries

/-!
# Strict E arithmetic after a coefficient shift

The factorial-series coefficients of the r-th derivative are a(n+r).
The complete arithmetic predicate survives every fixed shift: all algebraic
embeddings remain bounded, and d(n+r) clears every required initial segment.
-/
noncomputable section
namespace StrictEUnit

/-- Every fixed coefficient shift preserves all conjugate and denominator
conditions. If the original constant is C, the new one is C^(r+1). -/
theorem strictEArithmetic_shift {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (r : ℕ) :
    HasStrictEArithmetic (fun n => a (n + r)) := by
  obtain ⟨C, hC, hσ, d, hd, hdb, hi⟩ := ha
  have hpow (n : ℕ) : C ^ (n + r + 1) ≤ (C ^ (r + 1)) ^ (n + 1) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hC
    nlinarith
  refine ⟨C ^ (r + 1), one_le_pow₀ hC, ?_, (fun n => d (n + r)),
    (fun n => hd (n + r)), ?_, ?_⟩
  · intro σ n
    exact (hσ σ (n + r)).trans (hpow n)
  · intro n
    exact (hdb (n + r)).trans (hpow n)
  · intro n j hj
    exact hi (n + r) (j + r) (Nat.add_le_add_right hj r)

/-- In particular the genuine first-derivative coefficients have the complete
strict E arithmetic property, not only bounds in the chosen embedding. -/
theorem strictEArithmetic_derivative {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) : HasStrictEArithmetic (fun n => a (n + 1)) :=
  strictEArithmetic_shift ha 1

end StrictEUnit
