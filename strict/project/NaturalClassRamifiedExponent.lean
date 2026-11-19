import ActualGlobalRamifiedRow
noncomputable section
namespace StrictEUnit

theorem actualNaturalRoot_retained_exponent {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (xi : AlgebraicComplex)
    (i : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
    (j : Fin nu) (hj : j = e (naturalResonanceRootSeed _ xi
      (sameFourierEulerIndicial_ne_zero A hf hc) i)) :
    rho j = xi + (i.1.1 : AlgebraicComplex) := by
  rw [hj, hrho, Equiv.symm_apply_apply]
  rfl

theorem ramified_shift_quotient {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (hN : N ≠ 0) (m : ℤ) (s : ℕ) (xi rho : K)
    (hm : (m : K) / (N : K) = xi) (hr : rho = xi + (s : K)) :
    ((m + (N : ℤ) * (s : ℤ) : ℤ) : K) / (N : K) = rho := by
  rw [hr, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    add_div, hm]
  congr 1
  exact mul_div_cancel_left₀ (s : K) (Nat.cast_ne_zero.mpr hN)
end StrictEUnit
end
