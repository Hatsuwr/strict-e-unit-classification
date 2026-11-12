import LogFrameConstructedInverse
import AllClassFilteredSolutionDenominators

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Strengthened filtered-arithmetic criterion. The inverse, inverse pole bound,
lower-support bound, uniform log degree and finite-jet denominator are ALL
constructed from the actual frame. The still-unproved geometric input is
NONZERO DETERMINANT for a frame of the actual system over K. This does not
assert existence of that frame or arithmetic of unfiltered solutions. -/
theorem logFrame_filtered_solution_common_denominators {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ) (hB : 1≤B)
    (hden : ∀ M : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(M+1) ∧
      ∀ m,m≤M →∀ l,l≤M →∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0) :
    ∃ L : ℤ,∃ d : ℕ,∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,
      0<D ∧ (D : ℝ)≤E^(N+1) ∧ ∀ m,m≤N →∀ s i t,
      IsIntegral ℤ ((D : K)*((literalLogPolynomialFilter (rho s)
        (allClassPrefixFilter rho L m d) (Y i s)).coeff t).coeff ((m : ℤ)+L)) := by
  obtain ⟨L,d,hYlow,hYdeg⟩ := logFrame_exists_uniform_bounds Y
  obtain ⟨J,W,hJ,_,hJlow⟩ := logFrame_exists_inverse_with_fixed_pole_bound C rho Y hY hdet
  exact ⟨L,d,allClassPrefixFilter_filtered_solution_common_denominators C B hB hden rho hrho Y J
    hY hJ L (W : ℤ) d hYlow hYdeg hJlow⟩

end StrictEUnit
end
