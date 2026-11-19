import AugmentedSourceEulerSolutions
import SelectedSourceForcingArithmetic

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- The exact regular Euler matrix for the original augmented source inherits
common exponential divided-connection arithmetic by its PROVED natural gauge.
The Fourier companion plays no part in this transfer. -/
theorem selectedFuchsSourceData_augmented_euler_arithmetic
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) (d : ℕ) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
        (powerSeriesEulerDividedConnection (augmentedSourceEulerMatrix n t U d) m i j)) := by
  have hA := selectedFuchsSourceData_polynomial_forcing_arithmetic G a phi (n+1) hr c T UI E hsource d
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hV := companion_common_denominators_local_bounds n c _ _ hT hclear E hE hden
  exact monomialEulerPresentation_divided_arithmetic _ _ _
    (augmentedSourceEulerMatrix_realization n c _ _ hT hclear hV d) hA

/-- Arithmetic and exact scalar-solution identification for the SAME augmented
regular Euler matrix, retaining original source order and clearing tuple. -/
def SameClearingAugmentedSourceEulerData
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
  ∀ d : ℕ,
    (∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
        (powerSeriesEulerDividedConnection (augmentedSourceEulerMatrix n t U d) m i j))) ∧
    (∀ f : LaurentSeries K,
      (∀ i,laurentEuler (augmentedSourceEulerJet n c t f d i)=
        ∑ j,HahnSeries.ofPowerSeries ℤ K (augmentedSourceEulerMatrix n t U d i j)*
          augmentedSourceEulerJet n c t f d j) ↔
      (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1]
        (sourceCompanionResidual n (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j))
          (polynomialLaurentImage t) f)=0)

theorem selectedFuchsSourceData_augmented_euler_data
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    SameClearingAugmentedSourceEulerData n c T UI := by
  have harith := selectedFuchsSourceData_augmented_euler_arithmetic G a phi n hr c T UI E hsource
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hV := companion_common_denominators_local_bounds n c _ _ hT hclear E hE hden
  intro d
  exact ⟨harith d,fun f =>augmentedSourceEulerJet_solution_iff n c _ _ hT hclear hV f d⟩

end StrictEUnit
end
