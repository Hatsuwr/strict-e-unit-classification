import V5BroadArithmeticProduct
import V5BroadAlgebraicDescent

noncomputable section
open scoped BigOperators
namespace StrictEUnit

private theorem prefix_growth_mono (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 ≤ ε)
    {k n : ℕ} (hkn : k ≤ n) :
    C^(k+1)*(k.factorial : ℝ)^ε ≤ C^(n+1)*(n.factorial : ℝ)^ε := by
  apply mul_le_mul
  · exact pow_le_pow_right₀ hC (by omega)
  · exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le hkn) hε
  · positivity
  · positivity

/-- Broad arbitrary-epsilon arithmetic is stable under binomial convolution. -/
theorem v5_broad_algebraicArithmetic_binomialConvolution (a b : ℕ → AlgebraicComplex)
    (ha : V5BroadAlgebraicArithmetic a) (hb : V5BroadAlgebraicArithmetic b) :
    V5BroadAlgebraicArithmetic (v5BinomialConvolution a b) := by
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
  · intro τ n
    simp only [v5BinomialConvolution, map_sum, map_mul, map_natCast]
    have hterm (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
        ‖(n.choose k : ℂ)*τ (a k)*τ (b (n-k))‖ ≤
          (n.choose k:ℝ) * ((A*B)^(n+1)*(n.factorial:ℝ)^ε) := by
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hak := (haa τ k).trans (prefix_growth_mono A (ε/2) hA (by positivity) hkn)
      have hbk := (hbb τ (n-k)).trans (prefix_growth_mono B (ε/2) hB (by positivity) (Nat.sub_le _ _))
      calc
        _ = (n.choose k:ℝ) * (‖τ (a k)‖*‖τ (b (n-k))‖) := by simp [norm_mul]; ring
        _ ≤ (n.choose k:ℝ) * ((A^(n+1)*(n.factorial:ℝ)^(ε/2))*(B^(n+1)*(n.factorial:ℝ)^(ε/2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hak hbk (norm_nonneg _) (by positivity)) (by positivity)
        _ = _ := by rw [hfactor]
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖(n.choose k:ℂ)*τ (a k)*τ (b (n-k))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*((A*B)^(n+1)*(n.factorial:ℝ)^ε) := Finset.sum_le_sum hterm
      _ = (2:ℝ)^n * ((A*B)^(n+1)*(n.factorial:ℝ)^ε) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
      _ ≤ (2:ℝ)^(n+1) * ((A*B)^(n+1)*(n.factorial:ℝ)^ε) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · intro L n hn
    have he := v5_binomialConvolution_integral
      (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) da db hai hbi L n hn
    change IsIntegral ℤ ((↑(da L * db L) : ℂ) *
      (algebraicClosure ℚ ℂ).val (v5BinomialConvolution a b n))
    simpa only [v5BinomialConvolution, map_sum, map_mul, map_natCast] using he


#print axioms v5_broad_algebraicArithmetic_binomialConvolution
end StrictEUnit
