import TwistedSelectedNormalization

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

theorem twistedSelected_fourierLift_action {mu nu : ℕ} (rho : K)
    (a : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs a)
    (f : Polynomial (LaurentSeries K)) :
    scalarTwistedLogOperator nu (fun k =>(stage61_fourierLift a hf).coeff k.val) rho f=
      stage61_logZPow 1 ((nu:ℤ)-(mu:ℤ))*actualTwistedStage53Action rho a f := by
  classical
  unfold actualTwistedStage53Action
  rw [← actualTwistedLogOrdinary_stage53]
  simp only [Finset.mul_sum,← Algebra.smul_def,stage61_logScalar_mul,stage61_logCoordinate_pow]
  simp only [twisted_normalized_fourier_term]
  unfold scalarTwistedLogOperator
  have he : (actualTwistedEulerEnd rho : _ → _)=twistedLogPolynomialEuler rho :=
    funext (actualTwistedEulerEnd_apply rho)
  simp only [he,stage61_fourierLift,stage59_regularLift_map_coeff,
    stage61_fourierEulerSymbol_coeff,map_sum,Finset.sum_mul,
    stage61_logCoefficientMap_monomial,Nat.cast_one,one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem twistedSelected_fourierLift_zero_iff {mu nu : ℕ} (rho : K)
    (a : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs a)
    (f : Polynomial (LaurentSeries K)) :
    scalarTwistedLogOperator nu (fun k =>(stage61_fourierLift a hf).coeff k.val) rho f=0 ↔
      actualTwistedStage53Action rho a f=0 := by
  rw [twistedSelected_fourierLift_action,mul_eq_zero]
  have hz : stage61_logZPow (K:=K) 1 ((nu:ℤ)-(mu:ℤ))≠0 := by
    simp only [stage61_logZPow,ne_eq,map_eq_zero]
    exact HahnSeries.single_ne_zero one_ne_zero
  simp only [hz,false_or]

/-- The retained, existing selected amplitude solves the exact Stage53 tuple.
No new amplitude or annihilator is chosen. -/
theorem sameFourierTwistedAmplitude_stage53 {mu nu : ℕ}
    (a : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs a)
    (hc : a (Fin.last mu) (Fin.last nu)≠0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols a hf 0)) :
    actualTwistedStage53Action (frobeniusRootSeedExponent _ i) a
      (sameFourierTwistedAmplitude a hf i)=0 := by
  apply (twistedSelected_fourierLift_zero_iff _ a hf _).mp
  exact sameFourierTwistedAmplitude_equation a hf hc i

/-- The full generalized Fourier action annihilates the SAME selected amplitude. -/
theorem sameFourierTwistedAmplitude_generalizedArray {mu nu : ℕ}
    (a : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs a)
    (hc : a (Fin.last mu) (Fin.last nu)≠0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols a hf 0)) :
    generalizedLogFourierArrayAction (frobeniusRootSeedExponent _ i) a
      (logPolynomialToCoefficientSeries (sameFourierTwistedAmplitude a hf i))=0 := by
  rw [fullArray_stage53_solution_iff]
  exact sameFourierTwistedAmplitude_stage53 a hf hc i

end StrictEUnit
end
