import EulerAnalyticCoefficientDisk
import SelectedFuchsSourceData

noncomputable section
open scoped Topology BigOperators Matrix NumberField
namespace StrictEUnit

/-- An actual analytic realization of the SAME regular source Euler matrix,
for every complex coefficient embedding. Its PS coefficients and residue are
literal, and the original T clearing holds on a common derived positive disk.
This constructs coefficient functions, not a singular solution frame. -/
def SameClearingAnalyticEulerData
    {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  ∀ σ : K →+* ℂ,
    (∀ i j,HasFPowerSeriesAt (fun z => sameCompanionEulerAnalyticMatrix σ n t U z i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun m => PowerSeries.coeff ℂ m
        (PowerSeries.map σ (sameCompanionEulerPowerSeriesMatrix n t U i j)))) 0) ∧
    sameCompanionEulerAnalyticMatrix σ n t U 0=
      (regularCompanionResidue n (t.coeff t.natTrailingDegree)
        (polynomialCompanionFace n 1 1 t U)).map σ ∧
    ∃ ε : ℝ,0<ε ∧
      (∀ z ∈ Metric.ball (0:ℂ) ε,(sameCompanionEulerDenominatorPolynomial t).eval₂ σ z ≠ 0) ∧
      (∀ i j,AnalyticOnNhd ℂ (fun z => sameCompanionEulerAnalyticMatrix σ n t U z i j)
        (Metric.ball (0:ℂ) ε)) ∧
      ∀ z ∈ Metric.ball (0:ℂ) ε,∀ j : Fin (n+1),
        t.eval₂ σ z*sameCompanionEulerAnalyticLastRow σ n t U j z=
          z^(n+1-j.val)*(U (Fin.last n) j).eval₂ σ z

/-- The original source packet derives all inputs to the analytic realization;
no convergence, spectrum, solution-frame, new clearing or T(0)-unit input is
supplied. The ordinary-origin alternative is included unchanged. -/
theorem selectedFuchsSourceData_analyticEuler
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingAnalyticEulerData n T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hV := companion_common_denominators_local_bounds n c _ _ hT hclear E hE hden
  intro σ
  obtain ⟨ε,hε,hD,hA⟩ := sameCompanionEulerAnalyticMatrix_positive_disk σ n _ _ hT
  refine ⟨sameCompanionEulerAnalyticMatrix_hasFPowerSeriesAt σ n _ _ hT,
    sameCompanionEulerAnalyticMatrix_zero σ n _ _ hT,ε,hε,hD,hA,?_⟩
  intro z hz j
  exact sameCompanionEulerAnalyticLastRow_clearing σ n _ _ hV j z (hD z hz)

end StrictEUnit
end
