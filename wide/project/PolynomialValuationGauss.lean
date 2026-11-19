import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.RingTheory.Valuation.Basic
import Lean.Elab.Tactic.Omega

/-!
# A coefficient form of the polynomial Gauss lemma for valuations

This source-only component uses a unique dominant convolution coefficient.
It assumes neither a nontrivial valuation nor a UFD, number field, or Galois
extension. No norm, denominator, or connection-iterate conclusion is included.
-/

noncomputable section

open scoped BigOperators

namespace StrictEUnit

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- A nonzero polynomial has a least index attaining its largest coefficient
valuation. Earlier coefficients have strictly smaller valuation. -/
theorem polynomial_exists_least_maximal_valuation_coeff
    (v : Valuation K Γ₀) (p : Polynomial K) (hp : p ≠ 0) :
    ∃ a : ℕ, p.coeff a ≠ 0 ∧
      (∀ i : ℕ, v (p.coeff i) ≤ v (p.coeff a)) ∧
      (∀ i : ℕ, i < a → v (p.coeff i) < v (p.coeff a)) := by
  classical
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image p.support
    (fun i => v (p.coeff i)) (Polynomial.support_nonempty.mpr hp)
  have hk0 : p.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  have hle (i : ℕ) : v (p.coeff i) ≤ v (p.coeff k) := by
    by_cases hi : i ∈ p.support
    · exact hmax i hi
    · have hi0 : p.coeff i = 0 := Polynomial.not_mem_support_iff.mp hi
      rw [hi0, v.map_zero]
      exact zero_le'
  have hex : ∃ i : ℕ, v (p.coeff i) = v (p.coeff k) := ⟨k, rfl⟩
  let a := Nat.find hex
  have ha : v (p.coeff a) = v (p.coeff k) := Nat.find_spec hex
  refine ⟨a, ?_, ?_, ?_⟩
  · apply (v.ne_zero_iff).mp
    rw [ha]
    exact (v.ne_zero_iff).mpr hk0
  · intro i
    rw [ha]
    exact hle i
  · intro i hi
    have hne : v (p.coeff i) ≠ v (p.coeff k) := Nat.find_min hex hi
    rw [ha]
    exact lt_of_le_of_ne (hle i) hne

/-- The sum of the least maximizing indices gives a product coefficient with
valuation exactly the product of the two maximal valuations. -/
theorem polynomial_valuation_coeff_mul_at_least_maxima
    (v : Valuation K Γ₀) (p q : Polynomial K) (a b : ℕ)
    (ha0 : p.coeff a ≠ 0) (hb0 : q.coeff b ≠ 0)
    (ha : ∀ i : ℕ, v (p.coeff i) ≤ v (p.coeff a))
    (hb : ∀ j : ℕ, v (q.coeff j) ≤ v (q.coeff b))
    (halt : ∀ i : ℕ, i < a → v (p.coeff i) < v (p.coeff a))
    (hblt : ∀ j : ℕ, j < b → v (q.coeff j) < v (q.coeff b)) :
    v ((p * q).coeff (a + b)) = v (p.coeff a) * v (q.coeff b) := by
  classical
  have hva : 0 < v (p.coeff a) := zero_lt_iff.mpr ((v.ne_zero_iff).mpr ha0)
  have hvb : 0 < v (q.coeff b) := zero_lt_iff.mpr ((v.ne_zero_iff).mpr hb0)
  have hdom :
      v (∑ x ∈ Finset.antidiagonal (a + b), p.coeff x.1 * q.coeff x.2) =
        v (p.coeff a * q.coeff b) := by
    apply v.map_sum_eq_of_lt (j := (a, b))
    · exact Finset.mem_antidiagonal.mpr rfl
    · exact (v.ne_zero_iff).mpr (mul_ne_zero ha0 hb0)
    · intro x hx
      have hx' := (@Finset.mem_sdiff (ℕ × ℕ) (Classical.typeDecidableEq _)
        (Finset.antidiagonal (a + b)) {(a, b)} x).mp hx
      have hsum : x.1 + x.2 = a + b := Finset.mem_antidiagonal.mp hx'.1
      have hne : x ≠ (a, b) := by
        simpa only [Finset.mem_singleton] using hx'.2
      have hsmall : x.1 < a ∨ x.2 < b := by
        refine Classical.byContradiction (fun hh => ?_)
        have hx1 : a ≤ x.1 := le_of_not_gt (fun h => hh (Or.inl h))
        have hx2 : b ≤ x.2 := le_of_not_gt (fun h => hh (Or.inr h))
        apply hne
        apply Prod.ext <;> omega
      simp only [v.map_mul]
      rcases hsmall with hxa | hxb
      · calc
          v (p.coeff x.1) * v (q.coeff x.2) ≤
              v (p.coeff x.1) * v (q.coeff b) :=
            mul_le_mul_of_nonneg_left (hb x.2) zero_le'
          _ < v (p.coeff a) * v (q.coeff b) :=
            mul_lt_mul_of_pos_right (halt x.1 hxa) hvb
      · calc
          v (p.coeff x.1) * v (q.coeff x.2) ≤
              v (p.coeff a) * v (q.coeff x.2) :=
            mul_le_mul_of_nonneg_right (ha x.1) zero_le'
          _ < v (p.coeff a) * v (q.coeff b) :=
            mul_lt_mul_of_pos_left (hblt x.2 hxb) hva
  rw [Polynomial.coeff_mul]
  simpa only [v.map_mul] using hdom

/-- Every product of coefficient valuations is bounded by any uniform bound
for the valuations of the product polynomial's coefficients. Zero polynomials
are permitted, and the bound need not be positive. -/
theorem polynomial_valuation_coeff_product_le
    (v : Valuation K Γ₀) (p q : Polynomial K) (c : Γ₀)
    (hprod : ∀ k : ℕ, v ((p * q).coeff k) ≤ c) (i j : ℕ) :
    v (p.coeff i) * v (q.coeff j) ≤ c := by
  by_cases hp : p = 0
  · subst p
    simp only [Polynomial.coeff_zero, v.map_zero, zero_mul]
    exact zero_le'
  by_cases hq : q = 0
  · subst q
    simp only [Polynomial.coeff_zero, v.map_zero, mul_zero]
    exact zero_le'
  obtain ⟨a, ha0, ha, halt⟩ := polynomial_exists_least_maximal_valuation_coeff v p hp
  obtain ⟨b, hb0, hb, hblt⟩ := polynomial_exists_least_maximal_valuation_coeff v q hq
  calc
    v (p.coeff i) * v (q.coeff j) ≤ v (p.coeff a) * v (q.coeff b) := by
      exact (mul_le_mul_of_nonneg_right (ha i) zero_le').trans
        (mul_le_mul_of_nonneg_left (hb j) zero_le')
    _ = v ((p * q).coeff (a + b)) :=
      (polynomial_valuation_coeff_mul_at_least_maxima v p q a b
        ha0 hb0 ha hb halt hblt).symm
    _ ≤ c := hprod (a + b)

/-- It suffices to check the finitely many nonzero product coefficients. -/
theorem polynomial_valuation_coeff_product_le_of_support
    (v : Valuation K Γ₀) (p q : Polynomial K) (c : Γ₀)
    (hprod : ∀ k ∈ (p * q).support, v ((p * q).coeff k) ≤ c) (i j : ℕ) :
    v (p.coeff i) * v (q.coeff j) ≤ c := by
  apply polynomial_valuation_coeff_product_le v p q c ?_ i j
  intro k
  by_cases hk : k ∈ (p * q).support
  · exact hprod k hk
  · have hk0 : (p * q).coeff k = 0 := Polynomial.not_mem_support_iff.mp hk
    rw [hk0, v.map_zero]
    exact zero_le'

/-- Coefficientwise boundedness of a product is equivalent to boundedness of
all products of coefficients. At `c = 1`, this is the local integrality bridge. -/
theorem polynomial_valuation_coeff_product_le_iff
    (v : Valuation K Γ₀) (p q : Polynomial K) (c : Γ₀) :
    (∀ k : ℕ, v ((p * q).coeff k) ≤ c) ↔
      (∀ i j : ℕ, v (p.coeff i) * v (q.coeff j) ≤ c) := by
  constructor
  · intro h i j
    exact polynomial_valuation_coeff_product_le v p q c h i j
  · intro h k
    rw [Polynomial.coeff_mul]
    apply v.map_sum_le
    intro x hx
    rw [v.map_mul]
    exact h x.1 x.2

end StrictEUnit

end
