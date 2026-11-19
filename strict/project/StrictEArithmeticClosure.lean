import AlgebraicScalarExponential
import Mathlib.Data.Nat.Choose.Sum

/-!
# Arithmetic closure of strict E-function coefficients

These results prove closure of the complete arithmetic predicate. In particular,
all algebraic embeddings and positive integer common denominators are retained.
They do not assert differential-equation closure of strict E-functions.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Natural numbers are integral over the integers in the chosen embedding. -/
theorem strictE_natCast_isIntegral (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ)))

/-- Negation preserves the original arithmetic constant and denominators. -/
theorem strictEArithmetic_neg {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) : HasStrictEArithmetic (fun n => -a n) := by
  obtain ⟨A, hA, hσ, d, hd, hbound, hi⟩ := ha
  refine ⟨A, hA, ?_, d, hd, hbound, ?_⟩
  · intro σ n
    simpa only [map_neg, norm_neg] using hσ σ n
  · intro n j hj
    simpa only [IntermediateField.coe_neg, mul_neg] using (hi n j hj).neg

/-- Pointwise multiplication preserves both arithmetic conditions. -/
theorem strictEArithmetic_mul {a b : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (hb : HasStrictEArithmetic b) :
    HasStrictEArithmetic (fun n => a n * b n) := by
  obtain ⟨A, hA, hσa, da, hda, hba, hia⟩ := ha
  obtain ⟨B, hB, hσb, db, hdb, hbb, hib⟩ := hb
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, ?_,
    (fun n => da n * db n), (fun n => Nat.mul_pos (hda n) (hdb n)), ?_, ?_⟩
  · intro σ n
    simpa only [map_mul, norm_mul, mul_pow] using
      mul_le_mul (hσa σ n) (hσb σ n) (norm_nonneg _) (pow_nonneg hA0 _)
  · intro n
    simpa only [Nat.cast_mul, mul_pow] using
      mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (pow_nonneg hA0 _)
  · intro n j hj
    convert (hia n j hj).mul (hib n j hj) using 1
    simp only [Nat.cast_mul, IntermediateField.coe_mul]
    ring

/-- Addition uses the product of the two common integer denominators. -/
theorem strictEArithmetic_add {a b : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (hb : HasStrictEArithmetic b) :
    HasStrictEArithmetic (fun n => a n + b n) := by
  obtain ⟨A, hA, hσa, da, hda, hba, hia⟩ := ha
  obtain ⟨B, hB, hσb, db, hdb, hbb, hib⟩ := hb
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let C : ℝ := A + B + A * B
  have hsum : A + B ≤ C := le_add_of_nonneg_right (mul_nonneg hA0 hB0)
  have hprod : A * B ≤ C := le_add_of_nonneg_left (add_nonneg hA0 hB0)
  have hC : 1 ≤ C := hA.trans ((le_add_of_nonneg_right hB0).trans hsum)
  refine ⟨C, hC, ?_, (fun n => da n * db n),
    (fun n => Nat.mul_pos (hda n) (hdb n)), ?_, ?_⟩
  · intro σ n
    rw [map_add]
    calc
      ‖σ (a n) + σ (b n)‖ ≤ ‖σ (a n)‖ + ‖σ (b n)‖ := norm_add_le _ _
      _ ≤ A ^ (n + 1) + B ^ (n + 1) := add_le_add (hσa σ n) (hσb σ n)
      _ ≤ (A + B) ^ (n + 1) := pow_add_pow_le hA0 hB0 (by omega)
      _ ≤ C ^ (n + 1) := pow_le_pow_left₀ (add_nonneg hA0 hB0) hsum _
  · intro n
    calc
      ((da n * db n : ℕ) : ℝ) ≤ (A * B) ^ (n + 1) := by
        simpa only [Nat.cast_mul, mul_pow] using
          mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (pow_nonneg hA0 _)
      _ ≤ C ^ (n + 1) := pow_le_pow_left₀ (mul_nonneg hA0 hB0) hprod _
  · intro n j hj
    have h := ((strictE_natCast_isIntegral (db n)).mul (hia n j hj)).add
      ((strictE_natCast_isIntegral (da n)).mul (hib n j hj))
    convert h using 1
    simp only [Nat.cast_mul, IntermediateField.coe_add]
    ring

/-- Multiplication by any algebraic scalar is genuine arithmetic closure. -/
theorem strictEArithmetic_const_mul {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (α : AlgebraicComplex) :
    HasStrictEArithmetic (fun n => α * a n) := by
  have hα : HasStrictEArithmetic (fun _ : ℕ => α) := by
    simpa using algebraic_scalar_exp_arithmetic α 1
  exact strictEArithmetic_mul hα ha

/-- Subtraction retains all strict arithmetic requirements. -/
theorem strictEArithmetic_sub {a b : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (hb : HasStrictEArithmetic b) :
    HasStrictEArithmetic (fun n => a n - b n) := by
  simpa only [sub_eq_add_neg] using strictEArithmetic_add ha (strictEArithmetic_neg hb)

/-- The actual coefficient formula for the product of two factorial series. -/
def strictEBinomialConvolution (a b : ℕ → AlgebraicComplex) (n : ℕ) : AlgebraicComplex :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : AlgebraicComplex) * a k * b (n - k)

/-- A uniform geometric majorant for the binomial convolution. -/
theorem strictE_binomial_geometric_bound (a b : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (hb : ∀ n, ‖b n‖ ≤ C ^ (n + 1))
    (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * a k * b (n - k)‖ ≤
      (2 * C ^ 2) ^ (n + 1) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), ‖(n.choose k : ℂ) * a k * b (n - k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C ^ (n + 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (n.choose k : ℝ) * ‖a k‖ * ‖b (n - k)‖ ≤
            (n.choose k : ℝ) * C ^ (k + 1) * C ^ (n - k + 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (ha k) (Nat.cast_nonneg _))
            (hb (n - k)) (norm_nonneg _) (by positivity)
        _ = (n.choose k : ℝ) * C ^ (n + 2) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
    _ = (2 : ℝ) ^ n * C ^ (n + 2) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n
    _ ≤ (2 : ℝ) ^ (n + 1) * C ^ (2 * (n + 1)) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
        (pow_le_pow_right₀ hC (by omega)) (pow_nonneg hC0 _) (by positivity)
    _ = (2 * C ^ 2) ^ (n + 1) := by rw [mul_pow, ← pow_mul]

/-- The binomial convolution satisfies the complete strict E arithmetic
predicate. Its denominators are the products of the input denominators. -/
theorem strictEArithmetic_binomialConvolution {a b : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (hb : HasStrictEArithmetic b) :
    HasStrictEArithmetic (strictEBinomialConvolution a b) := by
  obtain ⟨A, hA, hσa, da, hda, hba, hia⟩ := ha
  obtain ⟨B, hB, hσb, db, hdb, hbb, hib⟩ := hb
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let M : ℝ := A * B
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA hB
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hAM : A ≤ M := le_mul_of_one_le_right hA0 hB
  have hBM : B ≤ M := le_mul_of_one_le_left hB0 hA
  have hMC : M ≤ 2 * M ^ 2 := by nlinarith
  refine ⟨2 * M ^ 2, hM.trans hMC, ?_, (fun n => da n * db n),
    (fun n => Nat.mul_pos (hda n) (hdb n)), ?_, ?_⟩
  · intro σ n
    simpa only [strictEBinomialConvolution, map_sum, map_mul, map_natCast] using
      strictE_binomial_geometric_bound (fun k => σ (a k)) (fun k => σ (b k)) M hM
        (fun k => (hσa σ k).trans (pow_le_pow_left₀ hA0 hAM _))
        (fun k => (hσb σ k).trans (pow_le_pow_left₀ hB0 hBM _)) n
  · intro n
    calc
      ((da n * db n : ℕ) : ℝ) ≤ M ^ (n + 1) := by
        simpa only [M, Nat.cast_mul, mul_pow] using
          mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (pow_nonneg hA0 _)
      _ ≤ (2 * M ^ 2) ^ (n + 1) := pow_le_pow_left₀ hM0 hMC _
  · intro n j hj
    change IsIntegral ℤ (((da n * db n : ℕ) : ℂ) *
      (algebraicClosure ℚ ℂ).val (strictEBinomialConvolution a b j))
    simp only [strictEBinomialConvolution, map_sum, map_mul, map_natCast,
      Nat.cast_mul, Finset.mul_sum]
    apply IsIntegral.sum
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hk : k ≤ n := hkj.trans hj
    have hsub : j - k ≤ n := (Nat.sub_le j k).trans hj
    have h := (strictE_natCast_isIntegral (j.choose k)).mul
      ((hia n k hk).mul (hib n (j - k) hsub))
    change IsIntegral ℤ ((da n : ℂ) * (db n : ℂ) *
      ((j.choose k : ℂ) * (a k : ℂ) * (b (j - k) : ℂ)))
    convert h using 1
    ring

end StrictEUnit

#print axioms StrictEUnit.strictE_natCast_isIntegral
#print axioms StrictEUnit.strictEArithmetic_neg
#print axioms StrictEUnit.strictEArithmetic_mul
#print axioms StrictEUnit.strictEArithmetic_add
#print axioms StrictEUnit.strictEArithmetic_const_mul
#print axioms StrictEUnit.strictEArithmetic_sub
#print axioms StrictEUnit.strictEBinomialConvolution
#print axioms StrictEUnit.strictE_binomial_geometric_bound
#print axioms StrictEUnit.strictEArithmetic_binomialConvolution
