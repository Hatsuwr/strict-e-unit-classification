import PolynomialHassePowerDivisibility
import Mathlib.RingTheory.Derivation.Basic

/-! Genuine polynomial-map compatibility for iterated and divided derivatives,
and an integral polynomial multiplier from Hasse power divisibility. -/

noncomputable section

namespace StrictEUnit

/-- First-derivative compatibility propagates to actual function iterates. -/
theorem derivation_iterate_polynomial_map
    {k R F : Type*} [CommSemiring k] [CommSemiring R] [CommSemiring F]
    [Algebra k F] (ι : Polynomial R →+* F) (d : Derivation k F F)
    (hcompat : ∀ P : Polynomial R, d (ι P) = ι P.derivative)
    (P : Polynomial R) (n : ℕ) :
    (d^[n]) (ι P) = ι ((Polynomial.derivative^[n]) P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        (congrArg d ih).trans (hcompat ((Polynomial.derivative^[n]) P))

/-- The polynomial Hasse derivative is derived from actual compatibility and
the factorial identity, not supplied as a rational-Hasse premise. -/
theorem derivation_divided_iterate_polynomial_map
    {k R F : Type*} [CommRing k] [CommSemiring R] [Field F] [CharZero F]
    [Algebra k F] (ι : Polynomial R →+* F) (d : Derivation k F F)
    (hcompat : ∀ P : Polynomial R, d (ι P) = ι P.derivative)
    (P : Polynomial R) (n : ℕ) :
    (d^[n]) (ι P) / (n.factorial : F) = ι (Polynomial.hasseDeriv n P) := by
  have hfac : n.factorial • Polynomial.hasseDeriv n P =
      (Polynomial.derivative^[n]) P := by
    simpa only [LinearMap.smul_apply] using
      congrFun (Polynomial.factorial_smul_hasseDeriv (R := R) n) P
  have hmap : (n.factorial : F) * ι (Polynomial.hasseDeriv n P) =
      (d^[n]) (ι P) := by
    calc
      (n.factorial : F) * ι (Polynomial.hasseDeriv n P) =
          ι (n.factorial • Polynomial.hasseDeriv n P) := by
        rw [map_nsmul, nsmul_eq_mul]
      _ = ι ((Polynomial.derivative^[n]) P) := congrArg ι hfac
      _ = (d^[n]) (ι P) := (derivation_iterate_polynomial_map ι d hcompat P n).symm
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).mpr
  exact hmap.symm.trans (mul_comm _ _)

/-- An entirely polynomial multiplier valid for every exponent and order.
No nonzero condition or division in the coefficient ring is used. -/
theorem exists_polynomial_hasse_power_multiplier
    {R : Type*} [CommSemiring R] (T : Polynomial R) (m a : ℕ) :
    ∃ B : Polynomial R,
      T ^ m * B = T ^ a * Polynomial.hasseDeriv a (T ^ m) := by
  by_cases ha : a ≤ m
  · obtain ⟨B, hB⟩ := polynomial_pow_sub_dvd_hasseDeriv_pow T m a
    refine ⟨B, ?_⟩
    have he : a + (m - a) = m := by omega
    rw [hB, ← mul_assoc, ← pow_add, he]
  · refine ⟨T ^ (a - m) * Polynomial.hasseDeriv a (T ^ m), ?_⟩
    have he : m + (a - m) = a := by omega
    rw [← mul_assoc, ← pow_add, he]

end StrictEUnit

end
