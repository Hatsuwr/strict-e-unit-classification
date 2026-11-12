import PolynomialTailAnalyticPreparation
import OrdinarySeriesInverseGerm

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

def sameCompanionEulerDenominatorPolynomial (T : Polynomial K) : Polynomial K :=
  polynomialTailPolynomial T.natTrailingDegree T

def sameCompanionEulerNumeratorPolynomial (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (j : Fin (n+1)) : Polynomial K :=
  polynomialTailPolynomial T.natTrailingDegree (Polynomial.X^(n+1-j.val)*U (Fin.last n) j)

def sameCompanionEulerAnalyticLastRow (σ : K →+* ℂ) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (j : Fin (n+1)) (z : ℂ) : ℂ :=
  (sameCompanionEulerNumeratorPolynomial n T U j).eval₂ σ z/
    (sameCompanionEulerDenominatorPolynomial T).eval₂ σ z

/-- Actual rational analytic coefficients in the original coordinate. This
is the coefficient matrix, not a fundamental solution frame. -/
def sameCompanionEulerAnalyticMatrix (σ : K →+* ℂ) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (z : ℂ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  constantCompanion n 1 (fun j => sameCompanionEulerAnalyticLastRow σ n T U j z)+
    Matrix.diagonal (fun j => (j.val:ℂ))

theorem sameCompanionEulerDenominatorPolynomial_eval_zero
    (σ : K →+* ℂ) (T : Polynomial K) :
    (sameCompanionEulerDenominatorPolynomial T).eval₂ σ 0=σ (T.coeff T.natTrailingDegree) := by
  rw [Polynomial.eval₂_at_zero]
  rw [sameCompanionEulerDenominatorPolynomial,polynomialTailPolynomial_coeff,Nat.zero_add]

theorem sameCompanionEulerDenominatorPolynomial_eval_zero_ne
    (σ : K →+* ℂ) (T : Polynomial K) (hT : T ≠ 0) :
    (sameCompanionEulerDenominatorPolynomial T).eval₂ σ 0 ≠ 0 := by
  rw [sameCompanionEulerDenominatorPolynomial_eval_zero]
  exact (map_ne_zero σ).2 (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT)

theorem sameCompanionEulerAnalyticLastRow_hasFPowerSeriesAt
    (σ : K →+* ℂ) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0) (j : Fin (n+1)) :
    HasFPowerSeriesAt (sameCompanionEulerAnalyticLastRow σ n T U j)
      (FormalMultilinearSeries.ofScalars ℂ (fun m => PowerSeries.coeff ℂ m
        (PowerSeries.map σ (sameCompanionEulerLastRowSeries n T U j)))) 0 := by
  let D := sameCompanionEulerDenominatorPolynomial T
  let N := sameCompanionEulerNumeratorPolynomial n T U j
  have hD : PowerSeries.map σ (sameCompanionEulerDenominatorSeries T)=(D.map σ:PowerSeries ℂ) :=
    polynomialTailPowerSeries_map σ _ _
  have hN : PowerSeries.map σ (sameCompanionEulerNumeratorSeries n T U j)=(N.map σ:PowerSeries ℂ) :=
    polynomialTailPowerSeries_map σ _ _
  have hD0 : PowerSeries.constantCoeff ℂ (D.map σ:PowerSeries ℂ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe,Polynomial.coeff_map]
    exact (map_ne_zero σ).2 (by
      change (polynomialTailPolynomial T.natTrailingDegree T).coeff 0 ≠ 0
      rw [polynomialTailPolynomial_coeff,Nat.zero_add]
      exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT)
  have he : PowerSeries.map σ (sameCompanionEulerLastRowSeries n T U j)=
      (N.map σ:PowerSeries ℂ)*(D.map σ:PowerSeries ℂ)⁻¹ := by
    rw [sameCompanionEulerLastRowSeries,map_mul,
      powerSeries_map_inv_of_constantCoeff_ne_zero σ _
        (sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT),hN,hD]
  have h := hasFPowerSeriesAt_div_ofScalars (fun z => (N.map σ).eval z)
    (fun z => (D.map σ).eval z) (N.map σ:PowerSeries ℂ) (D.map σ:PowerSeries ℂ)
    (hasFPowerSeriesAt_polynomial_ofScalars (N.map σ))
    (hasFPowerSeriesAt_polynomial_ofScalars (D.map σ)) hD0
  rw [← he] at h
  simpa only [Polynomial.eval_map] using h

/-- Every actual matrix entry has exactly the mapped original PS coefficients.
No regularity, growth, arithmetic-family or solution premise is needed. -/
theorem sameCompanionEulerAnalyticMatrix_hasFPowerSeriesAt
    (σ : K →+* ℂ) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (i j : Fin (n+1)) :
    HasFPowerSeriesAt (fun z => sameCompanionEulerAnalyticMatrix σ n T U z i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun m => PowerSeries.coeff ℂ m
        (PowerSeries.map σ (sameCompanionEulerPowerSeriesMatrix n T U i j)))) 0 := by
  classical
  have hc (c : ℂ) : HasFPowerSeriesAt (fun _ : ℂ => c)
      (FormalMultilinearSeries.ofScalars ℂ (fun m => PowerSeries.coeff ℂ m (PowerSeries.C ℂ c))) 0 := by
    simpa only [Polynomial.eval_C,Polynomial.coe_C] using
      hasFPowerSeriesAt_polynomial_ofScalars (Polynomial.C c)
  cases i using Fin.lastCases with
  | last =>
    have hr := sameCompanionEulerAnalyticLastRow_hasFPowerSeriesAt σ n T U hT j
    by_cases hj : Fin.last n=j
    · subst j
      simpa [sameCompanionEulerAnalyticMatrix,sameCompanionEulerPowerSeriesMatrix,
        constantCompanion,Matrix.diagonal_apply] using
          hasFPowerSeriesAt_add_ofScalars _ _ _ _ hr (hc (n:ℂ))
    · simpa [sameCompanionEulerAnalyticMatrix,sameCompanionEulerPowerSeriesMatrix,
        constantCompanion,Matrix.diagonal_apply,hj] using hr
  | cast i =>
    let c : K := (Pi.single i.succ (1:K) : Fin (n+1) → K) j+
      (if i.castSucc=j then (j.val:K) else 0)
    have hps : sameCompanionEulerPowerSeriesMatrix n T U i.castSucc j=PowerSeries.C K c := by
      simp only [sameCompanionEulerPowerSeriesMatrix,Matrix.add_apply,Fin.lastCases_castSucc,
        Matrix.diagonal_apply]
      by_cases hj : i.castSucc=j <;> simp [c,Pi.single_apply,hj]
    have han : (fun z => sameCompanionEulerAnalyticMatrix σ n T U z i.castSucc j)=
        (fun _ : ℂ => σ c) := by
      funext z
      simp only [sameCompanionEulerAnalyticMatrix,constantCompanion,Matrix.add_apply,
        Fin.lastCases_castSucc,Matrix.diagonal_apply]
      by_cases hj : i.castSucc=j <;> simp [c,Pi.single_apply,hj]
    rw [han,hps,PowerSeries.map_C]
    exact hc (σ c)

/-- Its actual value at zero is the literal previously checked residue. -/
theorem sameCompanionEulerAnalyticMatrix_zero
    (σ : K →+* ℂ) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0) :
    sameCompanionEulerAnalyticMatrix σ n T U 0=
      (regularCompanionResidue n (T.coeff T.natTrailingDegree)
        (polynomialCompanionFace n 1 1 T U)).map σ := by
  ext i j
  have he := hasFPowerSeriesAt_ofScalars_value_zero _ _
    (sameCompanionEulerAnalyticMatrix_hasFPowerSeriesAt σ n T U hT i j)
  have hr := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) K => σ (M i j))
    (sameCompanionEulerPowerSeriesMatrix_constantCoeff n T U)
  rw [he]
  change PowerSeries.constantCoeff ℂ (PowerSeries.map σ
    (sameCompanionEulerPowerSeriesMatrix n T U i j))=_
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map,
    Matrix.map_apply] using hr

end StrictEUnit
end
