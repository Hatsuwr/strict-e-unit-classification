import ActualFramePreimageArithmetic
import ActualZeroEulerSolution

noncomputable section
namespace StrictEUnit

def parallelSourceIndex {r : ℕ} (i : Fin r) : (s : ℕ) →Fin (r+s)
  | 0 =>i
  | s+1 =>(parallelSourceIndex i s).succ

theorem parallelForcingVector_source {R : Type*} {r : ℕ}
    (x : Fin r →R) (h : ℕ →R) (i : Fin r) (s : ℕ) :
    parallelForcingVector x h s (parallelSourceIndex i s)=x i := by
  induction s with
  | zero =>rfl
  | succ s ih =>exact ih

theorem finiteLaurentEulerWeights_source {r : ℕ}
    (w : Fin r →ℕ) (M : ℕ) (k : ℕ →ℤ) (i : Fin r) (s : ℕ) :
    finiteLaurentEulerWeights w M k s (parallelSourceIndex i s)=w i := by
  induction s with
  | zero =>rfl
  | succ s ih =>exact ih

variable {K : Type*} [Field K] [NumberField K]

/-- Extract the actual source's zeroth jet in the recursive forcing ordering,
then undo its monomial/reflection/reciprocal gauge. No component identity is
left as a premise here. The arithmetic of the complete actual solution is the
input to be obtained from its frame. -/
theorem actualParallelPreimage_extract_arithmetic
    (rho : K) (n s : ℕ) (u : LaurentSeries (Polynomial K))
    (h : ℕ →LaurentSeries (Polynomial K)) (w : Fin (n+1) →ℕ)
    (M : ℕ) (k : ℕ →ℤ)
    (harith : ∀ i,LogSeriesPrefixArithmetic
      (HahnSeries.single (finiteLaurentEulerWeights w M k s i:ℤ) (1:Polynomial K)*
        parallelForcingVector (generalizedLogOrdinaryJet rho n
          (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u))) h s i)) :
    LogSeriesPrefixArithmetic u := by
  have hi := harith (parallelSourceIndex (0 : Fin (n+1)) s)
  rw [finiteLaurentEulerWeights_source,parallelForcingVector_source] at hi
  simp only [generalizedLogOrdinaryJet,Fin.val_zero,Function.iterate_zero,id_eq] at hi
  rw [logLaurentCoefficientMap_reciprocalZ] at hi
  exact logSeriesPrefixArithmetic_undo_reflected_gauge u (w 0:ℤ) (-1) hi

end StrictEUnit
end
