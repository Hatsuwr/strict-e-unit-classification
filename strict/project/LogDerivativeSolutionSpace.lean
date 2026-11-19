import FrobeniusNaturalResonanceBasis

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem shiftedPolynomialDifferentialOperator_derivative
    (c : K) (P f : Polynomial K) :
    (shiftedPolynomialDifferentialOperator c P f).derivative=
      shiftedPolynomialDifferentialOperator c P f.derivative := by
  rw [shiftedPolynomialDifferentialOperator_eq]
  have h := polynomialDifferentialOperator_commute (Polynomial.X : Polynomial K)
    (P.comp (Polynomial.X+Polynomial.C c)) f
  simpa only [polynomialDifferentialOperator,Polynomial.aeval_X] using h

theorem polynomialLogEulerCoefficient_derivative (B : ℕ →Polynomial K)
    (rho : K) (u : ℕ →Polynomial K) (n : ℕ) :
    (polynomialLogEulerCoefficient B rho u n).derivative=
      polynomialLogEulerCoefficient B rho (fun m =>(u m).derivative) n := by
  unfold polynomialLogEulerCoefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact shiftedPolynomialDifferentialOperator_derivative _ _ _

/-- Log differentiation preserves the FULL equation-defined solution space. -/
def polynomialLogSolutionDerivative (B : ℕ →Polynomial K) (rho : K) :
    Module.End K (polynomialLogFormalSolutionSpace B rho) where
  toFun u := ⟨fun m =>(u.val m).derivative,by
    intro n
    rw [← polynomialLogEulerCoefficient_derivative,u.property n,map_zero]⟩
  map_add' u v := by apply Subtype.ext;funext m;exact map_add Polynomial.derivative _ _
  map_smul' c u := by apply Subtype.ext;funext m;exact map_smul Polynomial.derivative c _

/-- Completeness gives the unique constant matrix column for log derivative
of each retained natural-resonance basis vector. No closure premise is added. -/
theorem naturalResonanceFrobenius_log_derivative_expansion
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    ∃! c : polynomialLogResonanceCoordinateIndex rho (B 0) →K,
      (fun m =>(naturalResonanceFrobeniusCoefficients B rho j m).derivative)=
        ∑ i,c i • naturalResonanceFrobeniusCoefficients B rho i := by
  dsimp only
  apply polynomialLogFormalSolution_existsUnique_expansion r b rho hP
  intro m
  rw [← polynomialLogEulerCoefficient_derivative,
    naturalResonanceFrobeniusCoefficients_solution r b rho hP j m,map_zero]
end StrictEUnit
end
