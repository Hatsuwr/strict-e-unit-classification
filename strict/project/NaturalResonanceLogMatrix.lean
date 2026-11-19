import LogDerivativeNilpotent

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def naturalResonanceLogMatrix
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0) :
    Matrix (polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0))
      (polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) K :=
  LinearMap.toMatrix (naturalResonanceFrobeniusBasis r b rho hP)
    (naturalResonanceFrobeniusBasis r b rho hP)
    (polynomialLogSolutionDerivative
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) rho)

theorem naturalResonanceLogMatrix_isNilpotent
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0) :
    IsNilpotent (naturalResonanceLogMatrix r b rho hP) := by
  obtain ⟨d,hd⟩ := polynomialLogSolutionDerivative_isNilpotent r b rho hP
  refine ⟨d,?_⟩
  rw [naturalResonanceLogMatrix,LinearMap.toMatrix_pow,hd,map_zero]

/-- The actual square nilpotent matrix governing log differentiation, with
row-vector orientation u'=u*N and the original resonance indexing unchanged. -/
theorem naturalResonanceLogMatrix_equation
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) (m : ℕ) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    (naturalResonanceFrobeniusCoefficients B rho j m).derivative=
      ∑ i,(naturalResonanceLogMatrix r b rho hP i j) •
        naturalResonanceFrobeniusCoefficients B rho i m := by
  let basis := naturalResonanceFrobeniusBasis r b rho hP
  let D := polynomialLogSolutionDerivative
    (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) rho
  have he := basis.sum_repr (D (basis j))
  have hc := congrArg (fun u : polynomialLogFormalSolutionSpace
    (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) rho =>u.val m) he
  simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply] at hc
  dsimp only
  simpa only [naturalResonanceLogMatrix,LinearMap.toMatrix_apply,basis,
    naturalResonanceFrobeniusBasis_apply,D,polynomialLogSolutionDerivative,
    LinearMap.coe_mk,AddHom.coe_mk,naturalResonanceFrobeniusSolution] using hc.symm
theorem naturalResonanceLogMatrix_power_equation
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (d : ℕ) (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) (m : ℕ) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    (Polynomial.derivative : Polynomial K →Polynomial K)^[d]
      (naturalResonanceFrobeniusCoefficients B rho j m)=
      ∑ i,(((naturalResonanceLogMatrix r b rho hP)^d) i j) •
        naturalResonanceFrobeniusCoefficients B rho i m := by
  let basis := naturalResonanceFrobeniusBasis r b rho hP
  let D := polynomialLogSolutionDerivative
    (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) rho
  have he := basis.sum_repr ((D^d) (basis j))
  have hc := congrArg (fun u : polynomialLogFormalSolutionSpace
    (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) rho =>u.val m) he
  simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply] at hc
  dsimp only [D] at hc
  rw [polynomialLogSolutionDerivative_pow_coeff] at hc
  dsimp only
  simpa only [naturalResonanceLogMatrix,LinearMap.toMatrix_pow,LinearMap.toMatrix_apply,basis,
    D,polynomialLogSolutionDerivative_pow_coeff,naturalResonanceFrobeniusBasis_apply,polynomialLogSolutionDerivative,
    LinearMap.coe_mk,AddHom.coe_mk,naturalResonanceFrobeniusSolution] using hc.symm
end StrictEUnit
end
