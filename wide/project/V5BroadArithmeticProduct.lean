import V5BroadPowerArithmetic
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Factorial coefficients of a product of exponential generating series. -/
def v5BinomialConvolution (a b : ℕ → K) (n : ℕ) : K :=
  ∑ k ∈ Finset.range (n+1), (n.choose k : K) * a k * b (n-k)

omit [NumberField K] in
/-- The product of the two prefix denominators clears every product coefficient. -/
theorem v5_binomialConvolution_integral (a b : ℕ → K) (da db : ℕ → ℕ)
    (ha : ∀ L n, n ≤ L → IsIntegral ℤ ((da L : K)*a n))
    (hb : ∀ L n, n ≤ L → IsIntegral ℤ ((db L : K)*b n))
    (L n : ℕ) (hn : n ≤ L) :
    IsIntegral ℤ (((da L * db L : ℕ) : K) * v5BinomialConvolution a b n) := by
  unfold v5BinomialConvolution
  rw [Finset.mul_sum]
  apply IsIntegral.sum
  intro k hk
  have hkL : k ≤ L := by have := Finset.mem_range.mp hk; omega
  have hnk : n-k ≤ L := by omega
  have hc : IsIntegral ℤ (n.choose k : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (n.choose k : ℤ)))
  convert hc.mul ((ha L k hkL).mul (hb L (n-k) hnk)) using 1; push_cast; ring

private theorem prefix_growth_mono (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 ≤ ε)
    {k n : ℕ} (hkn : k ≤ n) :
    C^(k+1)*(k.factorial : ℝ)^ε ≤ C^(n+1)*(n.factorial : ℝ)^ε := by
  apply mul_le_mul
  · exact pow_le_pow_right₀ hC (by omega)
  · exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le hkn) hε
  · positivity
  · positivity

/-- Broad arbitrary-epsilon arithmetic is stable under binomial convolution. -/
theorem v5_broad_arithmetic_binomialConvolution (a b : ℕ → K)
    (ha : V5BroadArithmetic a) (hb : V5BroadArithmetic b) :
    V5BroadArithmetic (v5BinomialConvolution a b) := by
  intro ε hε
  obtain ⟨A,hA,da,hda,hdab,haa,hai⟩ := ha (ε/2) (by positivity)
  obtain ⟨B,hB,db,hdb,hdbb,hbb,hbi⟩ := hb (ε/2) (by positivity)
  have hAB : 1 ≤ A*B := one_le_mul_of_one_le_of_one_le hA hB
  have hC : 1 ≤ 2*(A*B) := by nlinarith
  have hfactor (n : ℕ) :
      (A^(n+1)*(n.factorial:ℝ)^(ε/2))*(B^(n+1)*(n.factorial:ℝ)^(ε/2)) =
      (A*B)^(n+1)*(n.factorial:ℝ)^ε := by
    have hr : (n.factorial:ℝ)^(ε/2) * (n.factorial:ℝ)^(ε/2) = (n.factorial:ℝ)^ε := by
      rw [← Real.rpow_add (by positivity), show ε/2+ε/2=ε by ring]
    rw [mul_pow]
    calc
      _ = (A^(n+1)*B^(n+1))*((n.factorial:ℝ)^(ε/2)*(n.factorial:ℝ)^(ε/2)) := by ring
      _ = _ := by rw [hr]
  refine ⟨2*(A*B),hC,fun L => da L*db L,fun L => Nat.mul_pos (hda L) (hdb L),?_,?_,?_⟩
  · intro L
    push_cast
    calc
      (da L:ℝ)*(db L:ℝ) ≤ _ := mul_le_mul (hdab L) (hdbb L) (by positivity) (by positivity)
      _ = (A*B)^(L+1)*(L.factorial:ℝ)^ε := hfactor L
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by nlinarith : A*B ≤ 2*(A*B)) _) (by positivity)
  · intro n
    have hterm (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
        NumberField.house ((n.choose k : K)*a k*b (n-k)) ≤
          (n.choose k:ℝ) * ((A*B)^(n+1)*(n.factorial:ℝ)^ε) := by
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hak := (haa k).trans (prefix_growth_mono A (ε/2) hA (by positivity) hkn)
      have hbk := (hbb (n-k)).trans (prefix_growth_mono B (ε/2) hB (by positivity) (Nat.sub_le _ _))
      have hchoose : NumberField.house (n.choose k : K) = (n.choose k:ℝ) := by
        simpa using (NumberField.house_intCast (K := K) (n.choose k : ℤ))
      calc
        _ ≤ NumberField.house (n.choose k:K) * NumberField.house (a k) * NumberField.house (b (n-k)) :=
          (NumberField.house_mul_le _ _).trans (mul_le_mul_of_nonneg_right (NumberField.house_mul_le _ _) (NumberField.house_nonneg _))
        _ = (n.choose k:ℝ) * (NumberField.house (a k)*NumberField.house (b (n-k))) := by rw [hchoose]; ring
        _ ≤ (n.choose k:ℝ) * ((A^(n+1)*(n.factorial:ℝ)^(ε/2))*(B^(n+1)*(n.factorial:ℝ)^(ε/2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hak hbk (NumberField.house_nonneg _) (by positivity)) (by positivity)
        _ = _ := by rw [hfactor]
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), NumberField.house ((n.choose k:K)*a k*b (n-k)) := NumberField.house_sum_le_sum_house _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*((A*B)^(n+1)*(n.factorial:ℝ)^ε) := Finset.sum_le_sum hterm
      _ = (2:ℝ)^n * ((A*B)^(n+1)*(n.factorial:ℝ)^ε) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
      _ ≤ (2:ℝ)^(n+1) * ((A*B)^(n+1)*(n.factorial:ℝ)^ε) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · exact v5_binomialConvolution_integral a b da db hai hbi

#print axioms v5_binomialConvolution_integral
#print axioms v5_broad_arithmetic_binomialConvolution
end StrictEUnit
