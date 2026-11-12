import PolynomialHasseMapBridge
import DerivationDividedLeibniz

/-!
# Polynomial representation of a cleared divided quotient derivative

The map and its actual first-derivative compatibility are explicit hypotheses.
The Hasse compatibility, divided product identity, and polynomial multipliers
are proved dependencies. No target-field linearity of the derivation or
constant-term/unit condition on the denominator is assumed.
-/

noncomputable section

open scoped BigOperators

namespace StrictEUnit

/-- For the SAME numerator and denominator, every cleared divided derivative
has a polynomial preimage over the original coefficient ring. This is generic
map compatibility; the actual Stage14 specialization is a separate obligation. -/
theorem exists_polynomial_scaled_divided_quotient
    {k R F : Type*} [CommRing k] [CommRing R] [Field F] [CharZero F]
    [Algebra k F] (ι : Polynomial R →+* F) (d : Derivation k F F)
    (hcompat : ∀ P : Polynomial R, d (ι P) = ι P.derivative)
    (T : Polynomial R) (hT : ι T ≠ 0) (P : Polynomial R) (m t : ℕ) :
    ∃ U : Polynomial R,
      ι U = (ι T) ^ (m + t) * (d^[t]) (ι P / (ι T) ^ m) / (t.factorial : F) := by
  let f : F := ι P / (ι T) ^ m
  have hquot : (ι T) ^ m * f = ι P := by
    exact (mul_comm _ _).trans (div_mul_cancel₀ (ι P) (pow_ne_zero m hT))
  have hpoly (a : ℕ) :
      (d^[a]) ((ι T) ^ m) / (a.factorial : F) =
        ι (Polynomial.hasseDeriv a (T ^ m)) := by
    simpa only [map_pow] using derivation_divided_iterate_polynomial_map
      ι d hcompat (T ^ m) a
  have hmem (n : ℕ) :
      (ι T) ^ (m + n) * ((d^[n]) f / (n.factorial : F)) ∈ ι.range := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            simpa only [Nat.add_zero, Function.iterate_zero_apply, Nat.factorial_zero,
              Nat.cast_one, div_one, hquot] using ι.mem_range_self P
        | succ n =>
            have hleib := derivation_divided_iterate_mul_antidiagonal
              d (n + 1) ((ι T) ^ m) f
            rw [hquot, derivation_divided_iterate_polynomial_map ι d hcompat P (n + 1)]
              at hleib
            simp_rw [hpoly] at hleib
            rw [Finset.Nat.sum_antidiagonal_succ] at hleib
            simp only [Polynomial.hasseDeriv_zero', map_pow] at hleib
            have hscaled := congrArg (fun z : F => (ι T) ^ (n + 1) * z) hleib
            dsimp only at hscaled
            rw [mul_add, Finset.mul_sum] at hscaled
            have hsum :
                (∑ ab ∈ Finset.antidiagonal n,
                  (ι T) ^ (n + 1) *
                    (ι (Polynomial.hasseDeriv (ab.1 + 1) (T ^ m)) *
                      ((d^[ab.2]) f / (ab.2.factorial : F)))) ∈ ι.range := by
              apply ι.range.sum_mem
              rintro ⟨a, b⟩ hab
              have habsum : a + b = n := Finset.mem_antidiagonal.mp hab
              have hb : b < n + 1 := by omega
              obtain ⟨B, hB⟩ := exists_polynomial_hasse_power_multiplier T m (a + 1)
              have hBm : (ι T) ^ m * ι B =
                  (ι T) ^ (a + 1) * ι (Polynomial.hasseDeriv (a + 1) (T ^ m)) := by
                simpa only [map_mul, map_pow] using congrArg ι hB
              have hterm :
                  (ι T) ^ (n + 1) * ι (Polynomial.hasseDeriv (a + 1) (T ^ m)) =
                    ι B * (ι T) ^ (m + b) := by
                calc
                  (ι T) ^ (n + 1) * ι (Polynomial.hasseDeriv (a + 1) (T ^ m)) =
                      (ι T) ^ b * ((ι T) ^ (a + 1) *
                        ι (Polynomial.hasseDeriv (a + 1) (T ^ m))) := by
                    rw [← mul_assoc, ← pow_add, show b + (a + 1) = n + 1 by omega]
                  _ = (ι T) ^ b * ((ι T) ^ m * ι B) := by rw [← hBm]
                  _ = ι B * (ι T) ^ (m + b) := by rw [pow_add]; ring
              rw [← mul_assoc, hterm, mul_assoc]
              exact ι.range.mul_mem (ι.mem_range_self B) (ih b hb)
            have hleft :
                (ι T) ^ (n + 1) * ι (Polynomial.hasseDeriv (n + 1) P) ∈ ι.range := by
              simpa only [map_mul, map_pow] using
                ι.mem_range_self (T ^ (n + 1) * Polynomial.hasseDeriv (n + 1) P)
            have hmain := ι.range.sub_mem hleft hsum
            rw [hscaled, add_sub_cancel_right] at hmain
            simpa only [← mul_assoc, ← pow_add, Nat.add_comm (n + 1) m] using hmain
  obtain ⟨U, hU⟩ := hmem t
  refine ⟨U, ?_⟩
  simpa only [f, mul_div_assoc] using hU

end StrictEUnit

end
