import OriginalSourceLaurentUnitPresentation
import SelectedFiniteLaurentForcingArithmetic

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- The actual regular Euler presentation of every finite Laurent source
forcing extension inherits divided-connection arithmetic from the original
source, with a constructed natural gauge. No Fourier matrix is substituted. -/
theorem selectedFuchsSourceData_finite_laurent_unit_euler_arithmetic
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (k : ℕ →ℤ) (s : ℕ) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
    let M := finiteLaurentOffset k s
    let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n t U M)
      (augmentedSourceEulerColumn n t) (M+(n+1)) k s
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)) := by
  have hA := selectedFuchsSourceData_finite_laurent_forcing_arithmetic G a phi (n+1) hr c T UI E hsource k s
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hV := companion_common_denominators_local_bounds n c _ _ hT hclear E hE hden
  exact monomialEulerPresentation_divided_arithmetic _ _ _
    (originalSource_finite_laurent_unit_euler_presentation n c _ _ hT hclear hV k s) hA

end StrictEUnit
end
