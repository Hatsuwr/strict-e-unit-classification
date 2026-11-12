import FiniteSplittingActualSolutionArithmetic
import ParallelForcingIndexedAction

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A homogeneous source solution embeds in the actual one-mode extension
with zero forcing coordinate, independently of the forcing eigenvalue. -/
theorem homogeneousSource_zero_extension {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (a : PowerSeries K) (xi : K) (x : Fin r →LaurentSeries (Polynomial K))
    (hx : ∀ i,twistedPolynomialCoefficientEuler xi (x i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*x j) :
    ∀ i,twistedPolynomialCoefficientEuler xi (Fin.cases 0 x i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (forcingEulerBlock C g a i j))*Fin.cases 0 x j := by
  intro i
  cases i using Fin.cases with
  | zero =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero,forcingEulerBlock,Fin.cases_succ,map_zero,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
    apply HahnSeries.ext
    funext z
    rw [twistedPolynomialCoefficientEuler_coeff]
    simp
  | succ i =>
    rw [Fin.sum_univ_succ]
    simpa [forcingEulerBlock] using hx i

theorem homogeneousSource_from_extension_arithmetic {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (a : PowerSeries K) (hf : FiniteSplittingUnfilteredFrameData (forcingEulerBlock C g a))
    (xi : K) (x : Fin r →LaurentSeries (Polynomial K))
    (hx : ∀ i,twistedPolynomialCoefficientEuler xi (x i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*x j) :
    ∀ i,LogSeriesPrefixArithmetic (x i) := by
  let v : Fin (r+1) →LaurentSeries (Polynomial K) :=Fin.cases 0 x
  have he : ∀ i,twistedPolynomialCoefficientEuler xi (v i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (forcingEulerBlock C g a i j))*v j :=
    homogeneousSource_zero_extension C g a xi x hx
  have h := finiteSplittingFrame_actual_solution_arithmetic (r:=r+1) (forcingEulerBlock C g a) hf xi v he
  intro i
  exact h i.succ

end StrictEUnit
end
