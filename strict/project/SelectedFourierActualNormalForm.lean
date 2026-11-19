import SelectedFourierArithmeticFrame
import Stage41StrictSeriesRealization
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

theorem selectedFuchsSourceData_actual_scalarNormalForm
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (ha : HasStrictEArithmetic a) :
    ∃ m r : ℕ, ∃ c : (algebraicClosure ℚ ℂ).toSubfield,
    ∃ p : Fin (m+1) → Polynomial (algebraicClosure ℚ ℂ).toSubfield,
      0 < m ∧ Stage28MonomialLeadingODE (algebraicClosure ℚ ℂ).toSubfield m r c p
        (stage41_strictSeriesFunction a) ∧
      Nonempty (Stage33ScalarNormalForm (algebraicClosure ℚ ℂ).toSubfield m p) := by
  have hS := selectedFuchsSourceData_fourier_scalarNormalForm G a phi n hr c T UI E hsource
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hnuEq,hnuPos,hfinite,hcorner,hLap,hCoeff,hannF⟩ := hsource
  refine ⟨_,n+1,_,_,hnuPos,⟨stage61_fourierCorner_ne_zero _ hcorner,
    actualFourier_leading_monomial _ hfinite, ?_⟩,hS⟩
  exact (stage41_strictSeries_polynomial_ode_iff ha _ _).mp hannF
end StrictEUnit
end
