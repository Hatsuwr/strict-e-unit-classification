import NormalizedLogPrefixTransfer
import SelectedNormalizedMixingBound

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem normalizedLogLaplace_prefix_from_binomial_arithmetic
    {ι : Type*} [Fintype ι] (r : ι →K) (hr : JointBinomialPrefixDenominators r)
    (i : ι) (h : ∀ n : ℕ,r i+(n+1:ℕ)≠0)
    (u : LaurentSeries (Polynomial K)) (d : ℕ)
    (hd : ∀ n : ℕ,(u.coeff ((n:ℤ)+1)).natDegree≤d)
    (hu : LogSeriesPrefixArithmetic u)
 :
    ∃ A : ℝ,1≤A ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤A^(N+1) ∧
      ∀ n,n≤N →∀ t,IsIntegral ℤ ((D:K)*(n.factorial:K)*
        ((generalizedLogLaplaceSeries (r i) h u).coeff (n:ℤ)).coeff t) := by
  apply normalizedLogLaplace_prefix_transfer (r i) h u d hd hu
  obtain ⟨C,hC,hden⟩ := factorialLogMixing_shared_matrix_bound r hr d
  refine ⟨C,hC,fun N =>?_⟩
  obtain ⟨Q,hQ,hQb,hQi⟩ := hden N
  exact ⟨Q,hQ,hQb,fun n hn j hj t =>hQi i h n hn j hj t⟩
end StrictEUnit
end
