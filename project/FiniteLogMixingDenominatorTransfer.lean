import LogLaplaceFactorialNormalization
import LogSeriesGaugeArithmetic
import LogMixingModeLinearity

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Whole-polynomial normalized mixing; the logarithmic terms are retained. -/
def factorialLogMixingLinear (rho : K) (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0)
    (n : ℕ) : Polynomial K →ₗ[K] Polynomial K where
  toFun := factorialLogMixing rho n
  map_add' p q := by
    unfold factorialLogMixing
    have ha := logMixingMode_add rho h (n:ℤ) p q
    change logMixingForward rho n (p+q)=_ at ha
    rw [ha,smul_add]
    rfl
  map_smul' a p := by
    unfold factorialLogMixing
    have hs := logMixingMode_smul rho a h (n:ℤ) p
    change logMixingForward rho n (a • p)=_ at hs
    rw [hs,smul_comm]
    rfl

/-- Finite log-degree matrix denominators combine with input denominators
multiplicatively, without discarding any logarithmic coefficient. -/
theorem polynomialLinear_denominator_transfer (F : Polynomial K →ₗ[K] Polynomial K)
    (p : Polynomial K) (d : ℕ) (hd : p.natDegree≤d) (D Q : ℕ)
    (hp : ∀ j,IsIntegral ℤ ((D:K)*p.coeff j))
    (hF : ∀ j,j≤d →∀ t,IsIntegral ℤ ((Q:K)*(F (Polynomial.X^j)).coeff t)) :
    ∀ t,IsIntegral ℤ (((D*Q:ℕ):K)*(F p).coeff t) := by
  intro t
  have hexp : F p=∑ j ∈ p.support,p.coeff j • F (Polynomial.X^j) := by
    conv_lhs =>rw [← Polynomial.sum_C_mul_X_pow_eq p]
    simp only [Polynomial.sum_def,map_sum,← Polynomial.smul_eq_C_mul,map_smul]
  rw [hexp,Polynomial.finset_sum_coeff,Finset.mul_sum]
  apply IsIntegral.sum
  intro j hj
  rw [Polynomial.coeff_smul,smul_eq_mul,Nat.cast_mul]
  have hjd : j≤d := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hd
  convert (hp j).mul (hF j hjd t) using 1 <;> ring

/-- This is a transfer criterion, NOT a proof of the operator bound hmix.
It isolates exactly the outstanding full logarithmic mixing estimate. -/
theorem factorialLogMixing_denominator_transfer (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (n d D Q : ℕ) (p : Polynomial K)
    (hd : p.natDegree≤d) (hp : ∀ j,IsIntegral ℤ ((D:K)*p.coeff j))
    (hmix : ∀ j,j≤d →∀ t,
      IsIntegral ℤ ((Q:K)*(factorialLogMixing rho n (Polynomial.X^j)).coeff t)) :
    ∀ t,IsIntegral ℤ (((D*Q:ℕ):K)*(factorialLogMixing rho n p).coeff t) :=
  polynomialLinear_denominator_transfer (factorialLogMixingLinear rho h n) p d hd D Q hp hmix
end StrictEUnit
end
