import StrictEArithmeticClosure
import StrictETaylorRealization
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! NEW PROOF RECONSTRUCTION, not recovered historical source.
The factorial coefficients of division by X - 1, their tail estimate, and
preservation of all strict arithmetic conditions for rational coefficients. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

/-- Coefficients of the unique formal quotient by X - 1. -/
def strictEDivisionCoeff {K : Type*} [Ring K] (a : ℕ → K) : ℕ → K
  | 0 => -a 0
  | n + 1 => (n + 1 : K) * strictEDivisionCoeff a n - a (n + 1)

@[simp] theorem map_strictEDivisionCoeff {K L : Type*} [Ring K] [Ring L]
    (φ : K →+* L) (a : ℕ → K) (n : ℕ) :
    φ (strictEDivisionCoeff a n) = strictEDivisionCoeff (fun j => φ (a j)) n := by
  induction n with
  | zero => simp [strictEDivisionCoeff]
  | succ n ih => simp [strictEDivisionCoeff, ih]

/-- The finite prefix expression is used only for the exact tail identity;
its large apparent factorial growth is not used as the growth estimate. -/
theorem strictEDivisionCoeff_normalized {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (n : ℕ) :
    strictEDivisionCoeff a n / (n.factorial : K) =
      -∑ j ∈ Finset.range (n + 1), a j / (j.factorial : K) := by
  induction n with
  | zero => simp [strictEDivisionCoeff]
  | succ n ih =>
    have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hfac : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [strictEDivisionCoeff, Finset.sum_range_succ]
    rw [neg_add, ← ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring

/-- A vanishing sum at one expresses the quotient coefficient as a small tail. -/
theorem strictEDivisionCoeff_tail_hasSum (a : ℕ → ℂ)
    (hzero : HasSum (fun j => a j / (j.factorial : ℂ)) 0) (n : ℕ) :
    HasSum (fun j => (n.factorial : ℂ) *
      (a (j + (n + 1)) / ((j + (n + 1)).factorial : ℂ)))
      (strictEDivisionCoeff a n) := by
  have ht := (hasSum_nat_add_iff' (f := fun j => a j / (j.factorial : ℂ))
    (n + 1)).mpr hzero
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (n.factorial : ℂ) *
      (0 - ∑ j ∈ Finset.range (n + 1), a j / (j.factorial : ℂ)) =
      strictEDivisionCoeff a n := by
    rw [zero_sub, ← strictEDivisionCoeff_normalized a n]
    exact mul_div_cancel₀ _ hn
  simpa only [he] using ht.mul_left (n.factorial : ℂ)

/-- The tail's factorial ratio is bounded by the reciprocal of j!. -/
theorem strictEDivisionCoeff_tail_term_bound (a : ℕ → ℂ) (C : ℝ)
    (hC : 1 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (n j : ℕ) :
    ‖(n.factorial : ℂ) * (a (j + (n + 1)) /
      ((j + (n + 1)).factorial : ℂ))‖ ≤
      C ^ (n + 2) * (C ^ j / (j.factorial : ℝ)) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hfacN : n.factorial * j.factorial ≤ (j + (n + 1)).factorial := by
    exact (Nat.le_of_dvd (Nat.factorial_pos (n + j))
      (Nat.factorial_mul_factorial_dvd_factorial_add n j)).trans
      (Nat.factorial_le (by omega))
  have hfac : (n.factorial : ℝ) * (j.factorial : ℝ) ≤
      ((j + (n + 1)).factorial : ℝ) := by exact_mod_cast hfacN
  calc
    _ = (n.factorial : ℝ) * ‖a (j + (n + 1))‖ /
        ((j + (n + 1)).factorial : ℝ) := by
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
      ring
    _ ≤ (n.factorial : ℝ) * C ^ (j + (n + 1) + 1) /
        ((j + (n + 1)).factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ha _) hn.le) (by positivity)
    _ ≤ (n.factorial : ℝ) * C ^ (j + (n + 1) + 1) /
        ((n.factorial : ℝ) * (j.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hn hj) hfac
    _ = C ^ (n + 2) * (C ^ j / (j.factorial : ℝ)) := by
      have he : j + (n + 1) + 1 = (n + 2) + j := by omega
      rw [he, pow_add]
      field_simp
      <;> ring

/-- The zero at one removes the apparent factorial growth of the prefix. -/
theorem strictEDivisionCoeff_geometric_bound (a : ℕ → ℂ) (C : ℝ)
    (hC : 1 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1))
    (hzero : HasSum (fun j => a j / (j.factorial : ℂ)) 0) (n : ℕ) :
    ‖strictEDivisionCoeff a n‖ ≤ (C ^ 2 * Real.exp C) ^ (n + 1) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have he : 1 ≤ Real.exp C := Real.one_le_exp hC0
  have hsum : HasSum (fun j : ℕ => C ^ j / (j.factorial : ℝ)) (Real.exp C) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp ℝ C
  have hb := (strictEDivisionCoeff_tail_hasSum a hzero n).norm_le_of_bounded
    (hsum.mul_left (C ^ (n + 2))) (strictEDivisionCoeff_tail_term_bound a C hC ha n)
  calc
    _ ≤ C ^ (n + 2) * Real.exp C := hb
    _ ≤ C ^ (2 * (n + 1)) * Real.exp C ^ (n + 1) :=
      mul_le_mul (pow_le_pow_right₀ hC (by omega))
        (by simpa only [pow_one] using pow_le_pow_right₀ he (show 1 ≤ n + 1 by omega))
        (Real.exp_pos C).le (pow_nonneg hC0 _)
    _ = _ := by rw [mul_pow, ← pow_mul]

/-- The coefficient witness of a given entire factorial representation is
unique. Consequently its arithmetic is inherited from any strict-E witness. -/
theorem strictEArithmetic_of_factorial_representation {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (a : ℕ → AlgebraicComplex)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) :
    HasStrictEArithmetic a := by
  obtain ⟨b, hd, hb, _, hab⟩ := hf
  have heq : a = b := by
    funext n
    apply Subtype.ext
    apply (div_left_inj' (show (n.factorial : ℂ) ≠ 0 by
      exact_mod_cast Nat.factorial_ne_zero n)).mp
    have hc (c : ℕ → AlgebraicComplex)
        (hc : ∀ z, HasSum (fun j => (c j : ℂ) * z ^ j / (j.factorial : ℂ)) (f z)) :
        entireCauchyCoefficient f n = (c n : ℂ) / (n.factorial : ℂ) := by
      apply entireCauchyCoefficient_eq_of_hasSum hd
      intro z
      convert hc z using 1
      funext j
      ring
    exact (hc a hs).symm.trans (hc b hb)
  simpa only [heq] using hab

/-- Rational coefficients are fixed by every algebraic embedding. -/
theorem strictE_rational_coeff_embedding (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (σ : AlgebraicComplex →ₐ[ℚ] ℂ) (n : ℕ) : σ (a n) = (a n : ℂ) := by
  obtain ⟨q, hq⟩ := hrat n
  rw [hq, σ.commutes]
  exact ((algebraicClosure ℚ ℂ).val.commutes q).symm

/-- Division keeps the original positive common denominators. The rational
hypothesis is used precisely to turn the chosen tail estimate into every
embedding estimate. -/
theorem strictEArithmetic_divisionCoeff (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hzero : HasSum (fun j => (a j : ℂ) / (j.factorial : ℂ)) 0) :
    HasStrictEArithmetic (strictEDivisionCoeff a) := by
  obtain ⟨C, hC, hσ, d, hd, hdb, hint⟩ := ha
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have he : 1 ≤ Real.exp C := Real.one_le_exp hC0
  have hCC : C ≤ C ^ 2 * Real.exp C := by
    calc
      C ≤ C ^ 2 := by nlinarith
      _ ≤ C ^ 2 * Real.exp C := le_mul_of_one_le_right (sq_nonneg C) he
  refine ⟨C ^ 2 * Real.exp C, hC.trans hCC, ?_, d, hd, ?_, ?_⟩
  · intro σ n
    change ‖σ.toRingHom (strictEDivisionCoeff a n)‖ ≤ _
    rw [map_strictEDivisionCoeff]
    have hmap : (fun j => σ (a j)) = (fun j => (a j : ℂ)) := by
      funext j
      exact strictE_rational_coeff_embedding a hrat σ j
    change ‖strictEDivisionCoeff (fun j => σ (a j)) n‖ ≤ _
    rw [hmap]
    exact strictEDivisionCoeff_geometric_bound (fun j => (a j : ℂ)) C hC
      (hσ (algebraicClosure ℚ ℂ).val) hzero n
  · intro n
    exact (hdb n).trans (pow_le_pow_left₀ hC0 hCC _)
  · intro n j
    induction j with
    | zero =>
      intro hj
      simpa only [strictEDivisionCoeff, IntermediateField.coe_neg, mul_neg] using
        (hint n 0 hj).neg
    | succ j ih =>
      intro hj
      have h := ((strictE_natCast_isIntegral (j + 1)).mul
        (ih (Nat.le_trans (Nat.le_succ j) hj))).sub (hint n (j + 1) hj)
      convert h using 1
      change (d n : ℂ) * (algebraicClosure ℚ ℂ).val.toRingHom
        (strictEDivisionCoeff a (j + 1)) = _
      simp only [strictEDivisionCoeff, map_sub, map_mul, map_add, map_natCast, map_one]
      change (d n : ℂ) *
          ((j + 1 : ℂ) * ((strictEDivisionCoeff (K := AlgebraicComplex) a j : AlgebraicComplex) : ℂ) - (a (j + 1) : ℂ)) =
        ((j + 1 : ℕ) : ℂ) * ((d n : ℂ) * ((strictEDivisionCoeff (K := AlgebraicComplex) a j : AlgebraicComplex) : ℂ)) -
          (d n : ℂ) * (a (j + 1) : ℂ)
      push_cast
      ring

end StrictEUnit
