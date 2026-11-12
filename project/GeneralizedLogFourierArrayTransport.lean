import GeneralizedLogLaplaceLinear

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def generalizedLogSourceArrayAction {mu nu : ℕ}
    (rho : K) (A : Fin (mu+1) →Fin (nu+1) →K)
    (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  ∑ i,∑ j,A i j • logSourceZ^[j.val] ((reciprocalLogSeriesDerivative rho)^[i.val] s)

def generalizedLogFourierArrayAction {mu nu : ℕ}
    (rho : K) (A : Fin (mu+1) →Fin (nu+1) →K)
    (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  ∑ i,∑ j,A i j • (logTargetNegativeDerivative rho)^[j.val] (logTargetX^[i.val] s)

/-- The SAME polynomial source array transports exactly, in mixed order.
Identification with the existing Stage53 normal-order tuple is still separate. -/
theorem generalizedLogLaplace_same_array {mu nu : ℕ}
    (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (A : Fin (mu+1) →Fin (nu+1) →K) (s : LaurentSeries (Polynomial K)) :
    generalizedLogLaplaceLinear rho h (generalizedLogSourceArrayAction rho A s)=
      generalizedLogFourierArrayAction rho A (generalizedLogLaplaceLinear rho h s) := by
  have hz : ∀ n s,generalizedLogLaplaceLinear rho h (logSourceZ^[n] s)=
      (logTargetNegativeDerivative rho)^[n] (generalizedLogLaplaceLinear rho h s) := by
    intro n s
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',generalizedLogLaplaceLinear_Z,ih,Function.iterate_succ_apply']
  have hd : ∀ n s,generalizedLogLaplaceLinear rho h ((reciprocalLogSeriesDerivative rho)^[n] s)=
      logTargetX^[n] (generalizedLogLaplaceLinear rho h s) := by
    intro n s
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',generalizedLogLaplaceLinear_Dz,ih,Function.iterate_succ_apply']
  simp only [generalizedLogSourceArrayAction,generalizedLogFourierArrayAction,map_sum,map_smul,hz,hd]

/-- Noninteger solutions correspond exactly for the same mixed-order array;
no source forcing and no extra equation hypothesis is introduced. -/
theorem generalizedLogFourier_noninteger_solution_iff {mu nu : ℕ}
    (rho : K) (hni : ∀ z : ℤ,rho≠(z : K))
    (A : Fin (mu+1) →Fin (nu+1) →K) (s : LaurentSeries (Polynomial K)) :
    generalizedLogFourierArrayAction rho A
      (generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) s)=0 ↔
      generalizedLogSourceArrayAction rho A s=0 := by
  rw [← generalizedLogLaplace_same_array]
  exact generalizedLogLaplaceSeries_noninteger_kernel rho hni _

/-- In the zero class, a Fourier solution has a finite ordinary-polynomial
source residual, proved rather than assumed. -/
theorem generalizedLogFourier_zero_solution_polynomial_residual {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →K) (s : LaurentSeries (Polynomial K))
    (hs : generalizedLogFourierArrayAction 0 A
      (generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero s)=0) :
    ∃ P : Polynomial K,∀ k : ℤ,(generalizedLogSourceArrayAction 0 A s).coeff k=
      if k≤0 then Polynomial.C (P.coeff (-k).toNat) else 0 := by
  apply generalizedLogLaplaceSeries_kernel_finite_polynomial
  change generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero _=0
  rwa [generalizedLogLaplace_same_array]

end StrictEUnit
end
