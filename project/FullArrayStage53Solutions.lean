import FullArrayStage53Embedding

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

def actualTwistedStage53Action {mu nu : ℕ} (rho : K)
    (a : Fin (mu+1) → Fin (nu+1) → K) (f : Polynomial (LaurentSeries K)) :=
  ∑ l,Polynomial.aeval (stage38_sourceCoordinate (K:=K) 1) (stage53_fourierCoeff a l)*
    (actualTwistedLogOrdinary rho)^[l.val] f

theorem fullArray_stage53_solution_iff {mu nu : ℕ} (rho : K)
    (a : Fin (mu+1) → Fin (nu+1) → K) (f : Polynomial (LaurentSeries K)) :
    generalizedLogFourierArrayAction rho a (logPolynomialToCoefficientSeries f)=0 ↔
      actualTwistedStage53Action rho a f=0 := by
  rw [generalizedLogFourierArrayAction_stage53]
  exact logPolynomialToCoefficientSeries_injective.eq_iff' (map_zero _)

theorem actualTwistedLogOrdinary_integerGauge (rho : K) (s : ℤ)
    (f : Polynomial (LaurentSeries K)) :
    actualTwistedLogOrdinary rho (frobeniusIntegerShift s f)=
      frobeniusIntegerShift s (actualTwistedLogOrdinary (rho+(s:K)) f) := by
  rw [actualTwistedLogOrdinary_shiftedEuler,frobeniusIntegerShift_twistedEuler,
    actualTwistedLogOrdinary_shiftedEuler]
  simp only [frobeniusIntegerShift]
  ring

theorem actualTwistedStage53Action_integerGauge {mu nu : ℕ} (rho : K) (s : ℤ)
    (a : Fin (mu+1) → Fin (nu+1) → K) (f : Polynomial (LaurentSeries K)) :
    actualTwistedStage53Action rho a (frobeniusIntegerShift s f)=
      frobeniusIntegerShift s (actualTwistedStage53Action (rho+(s:K)) a f) := by
  have hi : ∀ n,(actualTwistedLogOrdinary rho)^[n] (frobeniusIntegerShift s f)=
      frobeniusIntegerShift s ((actualTwistedLogOrdinary (rho+(s:K)))^[n] f) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih,actualTwistedLogOrdinary_integerGauge,
        Function.iterate_succ_apply']
  unfold actualTwistedStage53Action
  simp_rw [hi]
  simp only [frobeniusIntegerShift,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- No homogeneous source assumption is inserted into the zero-class branch. -/
theorem actualStage53_zero_source_residual {mu nu : ℕ}
    (a : Fin (mu+1) → Fin (nu+1) → K) (f : Polynomial (LaurentSeries K))
    (s : LaurentSeries (Polynomial K))
    (hs : generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero s=
      logPolynomialToCoefficientSeries f)
    (hf : actualTwistedStage53Action 0 a f=0) :
    ∃ P : Polynomial K,∀ k : ℤ,(generalizedLogSourceArrayAction 0 a s).coeff k=
      if k≤0 then Polynomial.C (P.coeff (-k).toNat) else 0 := by
  apply generalizedLogFourier_zero_solution_polynomial_residual a s
  rw [hs,fullArray_stage53_solution_iff]
  exact hf

theorem actualStage53_noninteger_source_iff {mu nu : ℕ} (rho : K)
    (hni : ∀ z : ℤ,rho≠(z:K))
    (a : Fin (mu+1) → Fin (nu+1) → K) (f : Polynomial (LaurentSeries K))
    (s : LaurentSeries (Polynomial K))
    (hs : generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) s=
      logPolynomialToCoefficientSeries f) :
    actualTwistedStage53Action rho a f=0 ↔ generalizedLogSourceArrayAction rho a s=0 := by
  rw [← fullArray_stage53_solution_iff,← hs]
  exact generalizedLogFourier_noninteger_solution_iff rho hni a s

end StrictEUnit
end
