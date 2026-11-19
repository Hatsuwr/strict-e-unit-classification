import V5BroadCompanionLocalBounds
import V5BroadSameMatrixDenominators
import MinimalCompanionPowerSeriesClearing
import IntegralRationalMatrixClearing
import SameCompanionScalarTuple

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- Choose bounds for the fixed clearing from its finite coefficients and degrees. -/
private theorem v5_integral_clearing_bounds
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K)) :
    ∃ τ : ℕ, ∃ H : ℝ, 1 ≤ H ∧
      (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ ∧
      (∀ i j, (U i j).natDegree ≤ τ) ∧
      ∀ n, NumberField.house (T.coeff n : K) ≤ H := by
  classical
  let τ := (T.map (algebraMap (𝓞 K) K)).natDegree +
    ∑ ij : Fin r × Fin r, (U ij.1 ij.2).natDegree
  let H : ℝ := 1 + ∑ n ∈ T.support, NumberField.house (T.coeff n : K)
  have hsum : 0 ≤ ∑ n ∈ T.support, NumberField.house (T.coeff n : K) :=
    Finset.sum_nonneg (fun n _ => NumberField.house_nonneg _)
  refine ⟨τ,H,by dsimp [H]; linarith,?_,?_,?_⟩
  · dsimp [τ]; omega
  · intro i j
    have h := Finset.single_le_sum (f:=fun ij : Fin r × Fin r => (U ij.1 ij.2).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
    change (U i j).natDegree ≤ ∑ ij : Fin r × Fin r, (U ij.1 ij.2).natDegree at h
    dsimp [τ]; omega
  · intro n
    by_cases hn : n ∈ T.support
    · have h := Finset.single_le_sum (f:=fun n => NumberField.house (T.coeff n : K))
        (fun _ _ => NumberField.house_nonneg _) hn
      dsimp [H]; linarith
    · rw [Polynomial.not_mem_support_iff.mp hn]
      simpa only [NumberField.house, map_zero, norm_zero] using
        (zero_le_one.trans (show 1 ≤ H by dsimp [H]; linarith))

/-- Apply denominator growth to the very same cyclic companion that yields
the polynomial equation for the original Borel series. Neither regularity
nor independence of a separately chosen solution is assumed. -/
theorem v5_broad_borel_local_regularity_of_prefix
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (hdata : OrdinaryBorelMinimalCyclicData (HahnSeries.ofPowerSeries ℤ K G) (n+1) c)
    (hprefix : V5BroadIntegralPrefix K (ordinaryDerivativePrefix (n+1) G)) :
    ∃ q : Fin (n+1+1) → Polynomial K,
      q (Fin.last (n+1)) ≠ 0 ∧
      (∀ i, q i ≠ 0 →
        (q (Fin.last (n+1))).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+(n+1)) ∧
      ∑ i, (q i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] G = 0 := by
  classical
  let A := minimalDerivativeCompanion (n+1) c
  obtain ⟨_,_,_,_,_,_,T,UI,_,_,_,hT,hclear⟩ :=
    exists_integral_polynomial_matrix_clearing K (n+1) A
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  let t := T.map φ
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map φ)
  let f := ordinaryDerivativePrefix (n+1) G
  have hclear' : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j := hclear
  obtain ⟨hli,hf⟩ := minimal_companion_powerSeries_clearing G (n+1) c hdata t U hclear'
  have hT0 : typeIIRationalPolynomialMap φ T ≠ 0 := by
    intro hz
    apply hT
    apply RatFunc.algebraMap_injective (K:=K)
    simpa only [map_zero] using hz
  obtain ⟨τ,H,hH,hTτ,hUτ,hTH⟩ := v5_integral_clearing_bounds T U
  obtain ⟨E,hE,hden⟩ := v5_broad_same_matrix_denominators (Nat.succ_pos n) T U A f
    T.natDegree τ H hH hli hT0 hTτ hUτ le_rfl hTH hclear' hf hprefix
  have hval := v5_companion_square_factorial_denominators_local_bounds n c t U hT hclear' E hE hden
  have hi : (⟨n+1-1,by omega⟩ : Fin (n+1)) = Fin.last n := by
    apply Fin.ext
    simp
  refine ⟨sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U, ?_, ?_, ?_⟩
  · simpa only [sameCompanionScalarTuple, Fin.lastCases_last] using hT
  · intro i hq
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      have hne : U (Fin.last n) i ≠ 0 := by
        simpa only [sameCompanionScalarTuple, Fin.lastCases_castSucc, hi, neg_ne_zero] using hq
      simpa only [sameCompanionScalarTuple, Fin.lastCases_last, Fin.lastCases_castSucc,
        hi, Polynomial.natTrailingDegree_neg, Fin.coe_castSucc] using hval i hne
  · have h := hf (Fin.last n)
    simp only [ordinaryDerivativePrefix, Fin.val_last, ← Function.iterate_succ_apply'] at h
    rw [Fin.sum_univ_castSucc]
    simp only [sameCompanionScalarTuple, Fin.lastCases_castSucc, Fin.lastCases_last,
      Fin.coe_castSucc, Fin.val_last, hi, Polynomial.coe_neg, neg_mul, Finset.sum_neg_distrib]
    rw [h]
    exact neg_add_cancel _

#print axioms v5_broad_borel_local_regularity_of_prefix
end StrictEUnit
end
