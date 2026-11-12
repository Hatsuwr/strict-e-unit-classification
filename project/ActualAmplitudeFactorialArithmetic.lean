import NormalizedLogPrefixArithmetic
import RetainedFamilyPreimageArithmetic

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Exponential common-prefix denominators in the literal factorial-series
convention, simultaneously for all logarithmic coefficients. -/
def FactorialLogPrefixArithmetic (p : Polynomial (LaurentSeries K)) : Prop :=
  ∃ A : ℝ,1≤A ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤A^(N+1) ∧
    ∀ n,n≤N →∀ t,IsIntegral ℤ ((D:K)*(n.factorial:K)*(p.coeff t).coeff (n:ℤ))

theorem factorialLogPrefixArithmetic_of_preimage
    {ι : Type*} [Fintype ι] (r : ι →K) (hr : JointBinomialPrefixDenominators r)
    (i : ι) (h : ∀ n : ℕ,r i+(n+1:ℕ)≠0)
    (p : Polynomial (LaurentSeries K)) (u : LaurentSeries (Polynomial K)) (d : ℕ)
    (hu : generalizedLogLaplaceLinear (r i) h u=logPolynomialToCoefficientSeries p)
    (hd : ∀ m,(u.coeff m).natDegree≤d) (ha : LogSeriesPrefixArithmetic u) :
    FactorialLogPrefixArithmetic p := by
  obtain ⟨A,hA,hden⟩ := normalizedLogLaplace_prefix_from_binomial_arithmetic r hr i h u d
    (fun n =>hd _) ha
  refine ⟨A,hA,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro n hn t
  have he : generalizedLogLaplaceSeries (r i) h u=logPolynomialToCoefficientSeries p := hu
  have hi := hDi n hn t
  rw [he,logPolynomialToCoefficientSeries_double_coeff] at hi
  exact hi
end StrictEUnit
end
