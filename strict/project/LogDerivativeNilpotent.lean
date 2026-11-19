import LogDerivativeSolutionSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem polynomialLogSolutionDerivative_pow_coeff (B : ℕ →Polynomial K) (rho : K)
    (u : polynomialLogFormalSolutionSpace B rho) (d m : ℕ) :
    (((polynomialLogSolutionDerivative B rho)^d) u).val m=
      (Polynomial.derivative : Polynomial K →Polynomial K)^[d] (u.val m) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ',Module.End.mul_apply,Function.iterate_succ_apply']
    change ((((polynomialLogSolutionDerivative B rho)^d) u).val m).derivative=_
    rw [ih]

theorem naturalResonanceFrobeniusCoefficients_degree_bound
    (B : ℕ →Polynomial K) (rho : K)
    (i : polynomialLogResonanceCoordinateIndex rho (B 0)) (m : ℕ) :
    (naturalResonanceFrobeniusCoefficients B rho i m).natDegree≤
      i.2.val+(B 0).natDegree := by
  unfold naturalResonanceFrobeniusCoefficients naturalCoefficientShift
  split_ifs
  · simpa only [Polynomial.natDegree_X_pow] using
      polynomialLogFrobeniusCoefficient_uniform_degree B (rho+(i.1.val:K))
        (Polynomial.X^i.2.val) (m-i.1.val)
  · simp only [Polynomial.natDegree_zero];omega

/-- Actual log differentiation on the full equation-defined solution space
is nilpotent. The uniform exponent is derived from its finite retained basis. -/
theorem polynomialLogSolutionDerivative_isNilpotent
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0) :
    IsNilpotent (polynomialLogSolutionDerivative
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) rho) := by
  classical
  let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
  let I := polynomialLogResonanceCoordinateIndex rho (B 0)
  let d := Finset.univ.sup (fun i : I =>i.2.val+(B 0).natDegree)+1
  refine ⟨d,?_⟩
  apply (naturalResonanceFrobeniusBasis r b rho hP).ext
  intro i
  apply Subtype.ext
  funext m
  rw [polynomialLogSolutionDerivative_pow_coeff,naturalResonanceFrobeniusBasis_apply]
  change (Polynomial.derivative : Polynomial K →Polynomial K)^[d]
    (naturalResonanceFrobeniusCoefficients B rho i m)=0
  apply Polynomial.iterate_derivative_eq_zero
  have hi := Finset.le_sup (f:=fun i : I =>i.2.val+(B 0).natDegree) (Finset.mem_univ i)
  exact (naturalResonanceFrobeniusCoefficients_degree_bound B rho i m).trans_lt
    (lt_of_le_of_lt hi (Nat.lt_succ_self _))
end StrictEUnit
end
