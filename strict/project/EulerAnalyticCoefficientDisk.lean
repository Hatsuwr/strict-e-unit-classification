import EulerAnalyticCoefficientGerms
import Mathlib.Analysis.Analytic.Polynomial

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Literal finite tail factorization from proved lower coefficient vanishing. -/
theorem polynomialTailPolynomial_factor (d : ℕ) (P : Polynomial K)
    (hP : ∀ k,k<d → P.coeff k=0) :
    Polynomial.X^d*polynomialTailPolynomial d P=P := by
  ext k
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hdk : d≤k
  · rw [if_pos hdk,polynomialTailPolynomial_coeff,Nat.sub_add_cancel hdk]
  · rw [if_neg hdk,hP k (Nat.lt_of_not_ge hdk)]

/-- Finite polynomial factorization of the SAME unit tail, retaining T. -/
theorem sameCompanionEulerDenominatorPolynomial_factor (T : Polynomial K) :
    Polynomial.X^T.natTrailingDegree*sameCompanionEulerDenominatorPolynomial T=T := by
  exact polynomialTailPolynomial_factor _ _
    (fun k hk => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk)

theorem sameCompanionEulerNumeratorPolynomial_factor (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (j : Fin (n+1)) :
    Polynomial.X^T.natTrailingDegree*sameCompanionEulerNumeratorPolynomial n T U j=
      Polynomial.X^(n+1-j.val)*U (Fin.last n) j := by
  exact polynomialTailPolynomial_factor _ _
    (sameCompanionEuler_shifted_numerator_lower n T U hV j)

/-- Pointwise ORIGINAL-T clearing wherever the tail denominator is nonzero.
This includes zero itself, even when the original T vanishes there. -/
theorem sameCompanionEulerAnalyticLastRow_clearing (σ : K →+* ℂ)
    (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (j : Fin (n+1)) (z : ℂ)
    (hz : (sameCompanionEulerDenominatorPolynomial T).eval₂ σ z ≠ 0) :
    T.eval₂ σ z*sameCompanionEulerAnalyticLastRow σ n T U j z=
      z^(n+1-j.val)*(U (Fin.last n) j).eval₂ σ z := by
  have hd := congrArg (fun P : Polynomial K => P.eval₂ σ z)
    (sameCompanionEulerDenominatorPolynomial_factor T)
  have hn := congrArg (fun P : Polynomial K => P.eval₂ σ z)
    (sameCompanionEulerNumeratorPolynomial_factor n T U hV j)
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X] at hd hn
  unfold sameCompanionEulerAnalyticLastRow
  rw [div_eq_mul_inv,← hd]
  calc
    _ = (z^T.natTrailingDegree*(sameCompanionEulerNumeratorPolynomial n T U j).eval₂ σ z)*
        ((sameCompanionEulerDenominatorPolynomial T).eval₂ σ z*
          ((sameCompanionEulerDenominatorPolynomial T).eval₂ σ z)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hz,mul_one,hn]

theorem sameCompanionEulerAnalyticLastRow_analyticAt (σ : K →+* ℂ)
    (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (j : Fin (n+1)) (z : ℂ)
    (hz : (sameCompanionEulerDenominatorPolynomial T).eval₂ σ z ≠ 0) :
    AnalyticAt ℂ (sameCompanionEulerAnalyticLastRow σ n T U j) z := by
  have hN := (AnalyticOnNhd.eval_polynomial (𝕜:=ℂ)
    ((sameCompanionEulerNumeratorPolynomial n T U j).map σ)) z (Set.mem_univ z)
  have hD := (AnalyticOnNhd.eval_polynomial (𝕜:=ℂ)
    ((sameCompanionEulerDenominatorPolynomial T).map σ)) z (Set.mem_univ z)
  have hnz : ((sameCompanionEulerDenominatorPolynomial T).map σ).eval z ≠ 0 := by
    simpa only [Polynomial.eval_map] using hz
  simpa only [sameCompanionEulerAnalyticLastRow,Polynomial.eval_map,div_eq_mul_inv] using
    hN.mul (hD.fun_inv hnz)

theorem sameCompanionEulerAnalyticMatrix_analyticAt (σ : K →+* ℂ)
    (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (z : ℂ)
    (hz : (sameCompanionEulerDenominatorPolynomial T).eval₂ σ z ≠ 0)
    (i j : Fin (n+1)) :
    AnalyticAt ℂ (fun w => sameCompanionEulerAnalyticMatrix σ n T U w i j) z := by
  classical
  cases i using Fin.lastCases with
  | last =>
    simp only [sameCompanionEulerAnalyticMatrix,constantCompanion,Matrix.add_apply,
      Fin.lastCases_last]
    exact (sameCompanionEulerAnalyticLastRow_analyticAt σ n T U j z hz).add analyticAt_const
  | cast i =>
    simp only [sameCompanionEulerAnalyticMatrix,constantCompanion,Matrix.add_apply,
      Fin.lastCases_castSucc]
    exact analyticAt_const

/-- One internally derived positive disk makes the actual coefficient matrix
analytic. This is an existential radius, not an asserted effective bound. -/
theorem sameCompanionEulerAnalyticMatrix_positive_disk (σ : K →+* ℂ)
    (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0) :
    ∃ ε : ℝ,0<ε ∧
      (∀ z ∈ Metric.ball (0:ℂ) ε,(sameCompanionEulerDenominatorPolynomial T).eval₂ σ z ≠ 0) ∧
      ∀ i j,AnalyticOnNhd ℂ (fun z => sameCompanionEulerAnalyticMatrix σ n T U z i j)
        (Metric.ball (0:ℂ) ε) := by
  have hd0 := sameCompanionEulerDenominatorPolynomial_eval_zero_ne σ T hT
  have hd : ∀ᶠ z in nhds (0:ℂ),
      (sameCompanionEulerDenominatorPolynomial T).eval₂ σ z ≠ 0 := by
    have hh := ((sameCompanionEulerDenominatorPolynomial T).map σ).continuous.continuousAt.eventually_ne
      (by simpa only [Polynomial.eval_map] using hd0)
    simpa only [Polynomial.eval_map] using hh
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.1 hd
  refine ⟨ε,hε,hball,?_⟩
  intro i j z hz
  exact sameCompanionEulerAnalyticMatrix_analyticAt σ n T U z (hball hz) i j

end StrictEUnit
end
