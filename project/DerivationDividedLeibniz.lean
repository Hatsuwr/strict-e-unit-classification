import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Genuine iterated and divided Leibniz identities

The derivation is linear only over its stated base. The proof uses additivity,
natural-number scalar multiplication, and the actual Leibniz identity; it never
uses linearity over the differentiated field. No rational quotient-Hasse or
integral scaled-quotient conclusion is asserted in this component.
-/

noncomputable section

open scoped BigOperators

namespace StrictEUnit

/-- Raw binomial Leibniz formula. Natural-number scalar multiplication avoids
any unjustified assertion that the derivation is linear over its target. -/
theorem derivation_iterate_mul_antidiagonal
    {k F : Type*} [CommSemiring k] [CommSemiring F] [Algebra k F]
    (d : Derivation k F F) (n : ℕ) (x y : F) :
    (d^[n]) (x * y) =
      ∑ ab ∈ Finset.antidiagonal n,
        n.choose ab.1 • ((d^[ab.1]) x * (d^[ab.2]) y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_antidiagonal_choose_succ_nsmul
        (M := F) (fun i j => (d^[i]) x * (d^[j]) y) n]
      simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul,
        Derivation.leibniz, smul_eq_mul, nsmul_add, Finset.sum_add_distrib]
      refine congrArg₂ (fun u v : F => u + v) rfl ?_
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ hij
      rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm, mul_comm]

/-- Dividing the genuine binomial identity by `n!` yields the Hasse-style
antidiagonal product rule. Factorials are invertible in `F`, not necessarily
in the base ring `k`. -/
theorem derivation_divided_iterate_mul_antidiagonal
    {k F : Type*} [CommRing k] [Field F] [CharZero F] [Algebra k F]
    (d : Derivation k F F) (n : ℕ) (x y : F) :
    (d^[n]) (x * y) / (n.factorial : F) =
      ∑ ab ∈ Finset.antidiagonal n,
        ((d^[ab.1]) x / (ab.1.factorial : F)) *
          ((d^[ab.2]) y / (ab.2.factorial : F)) := by
  rw [derivation_iterate_mul_antidiagonal, Finset.sum_div]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  have hn : a + b = n := Finset.mem_antidiagonal.mp hab
  have ha0 : (a.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have hb0 : (b.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
  have hab0 : ((a + b).factorial : F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + b))
  simp only [nsmul_eq_mul]
  rw [← hn, Nat.cast_add_choose F]
  field_simp [ha0, hb0, hab0]
  <;> ring

end StrictEUnit

end
