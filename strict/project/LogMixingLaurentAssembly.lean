import LogMixingModeLinearity
import LogFrameFiniteBounds

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Signed mode action with support contained in the input Laurent support. -/
def logMixingCoefficientSeries (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) where
  coeff n := ((-1 : K)^n) • logMixingMode rho n (s.coeff n)
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn
    change s.coeff n≠0
    intro hz
    apply hn
    simp only [hz,logMixingMode_zero rho h,smul_zero])

/-- The source index k maps to target k-1; this shift is essential. -/
def generalizedLogLaplaceSeries (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  logMixingCoefficientSeries rho h (HahnSeries.single (-1 : ℤ) (1 : Polynomial K)*s)

theorem generalizedLogLaplaceSeries_coeff (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) (n : ℤ) :
    (generalizedLogLaplaceSeries rho h s).coeff n=
      ((-1 : K)^n) • logMixingMode rho n (s.coeff (n+1)) := by
  change ((-1 : K)^n) • logMixingMode rho n
    ((HahnSeries.single (-1 : ℤ) (1 : Polynomial K)*s).coeff n)=_
  have hi : n=(n+1)+(-1) := by omega
  conv_lhs => arg 2;arg 3;rw [hi,HahnSeries.coeff_single_mul_add]
  simp only [one_mul]

theorem generalizedLogLaplaceSeries_lower_bound (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) (L : ℤ)
    (hs : ∀ n,n<L →s.coeff n=0) :
    ∀ n,n<L-1 →(generalizedLogLaplaceSeries rho h s).coeff n=0 := by
  intro n hn
  rw [generalizedLogLaplaceSeries_coeff,hs (n+1) (by omega),logMixingMode_zero rho h,smul_zero]

theorem generalizedLogLaplaceSeries_degree_bound (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) (d : ℕ)
    (hs : ∀ n,(s.coeff n).natDegree≤d) :
    ∀ n,((generalizedLogLaplaceSeries rho h s).coeff n).natDegree≤d := by
  intro n
  rw [generalizedLogLaplaceSeries_coeff]
  exact (Polynomial.natDegree_smul_le _ _).trans ((logMixingMode_natDegree_le _ _ _).trans (hs _))

end StrictEUnit
end
