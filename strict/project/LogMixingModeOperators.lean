import PolynomialDifferentialRightInverse

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Inverse gamma-ratio jets above a chosen base mode; no transcendental
Gamma value is introduced. -/
def logMixingForward (rho : K) : ℕ →Polynomial K →Polynomial K
  | 0,p => p
  | n+1,p => polynomialShiftInverse (rho+(n+1 : ℕ)) (logMixingForward rho n p)

/-- Backward modes use multiplication, NEVER inversion of a zero factor. -/
def logMixingBackward (rho : K) : ℕ →Polynomial K →Polynomial K
  | 0,p => p
  | n+1,p => shiftedPolynomialDerivative (rho-(n : K)) (logMixingBackward rho n p)

theorem shiftedPolynomialDerivative_derivative (c : K) (p : Polynomial K) :
    shiftedPolynomialDerivative c p.derivative = (shiftedPolynomialDerivative c p).derivative := by
  simp [shiftedPolynomialDerivative_apply,Polynomial.derivative_add,Polynomial.derivative_smul]

theorem polynomialShiftInverse_derivative (c : K) (hc : c≠0) (p : Polynomial K) :
    polynomialShiftInverse c p.derivative = (polynomialShiftInverse c p).derivative := by
  apply shiftedPolynomialDerivative_injective c hc
  rw [polynomialShiftInverse_rightInverse c hc,shiftedPolynomialDerivative_derivative,
    polynomialShiftInverse_rightInverse c hc]

theorem logMixingForward_recurrence (rho : K) (n : ℕ)
    (hc : rho+(n+1 : ℕ)≠0) (p : Polynomial K) :
    shiftedPolynomialDerivative (rho+(n+1 : ℕ)) (logMixingForward rho (n+1) p)=
      logMixingForward rho n p := by
  exact polynomialShiftInverse_rightInverse _ hc _

theorem logMixingForward_derivative (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℕ) (p : Polynomial K) :
    logMixingForward rho n p.derivative=(logMixingForward rho n p).derivative := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [logMixingForward,ih,polynomialShiftInverse_derivative _ (h n)]
    rfl

theorem logMixingBackward_derivative (rho : K) (n : ℕ) (p : Polynomial K) :
    logMixingBackward rho n p.derivative=(logMixingBackward rho n p).derivative := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [logMixingBackward,ih,shiftedPolynomialDerivative_derivative]
    rfl

theorem logMixingBackward_zero_first (p : Polynomial K) :
    logMixingBackward (0 : K) 1 p=p.derivative := by
  simp [logMixingBackward]

/-- The first collision lowers logarithmic degree, instead of discarding
all logarithmic modes along with the ordinary polynomial kernel. -/
theorem logMixingBackward_zero_first_X :
    logMixingBackward (0 : K) 1 (Polynomial.X : Polynomial K)=1 := by
  simp [logMixingBackward_zero_first]

theorem logMixingForward_natDegree_le (rho : K) (n : ℕ) (p : Polynomial K) :
    (logMixingForward rho n p).natDegree≤p.natDegree := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (polynomialShiftInverse_natDegree_le _ _).trans ih

theorem logMixingBackward_natDegree_le (rho : K) (n : ℕ) (p : Polynomial K) :
    (logMixingBackward rho n p).natDegree≤p.natDegree := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _) |>.trans ih)
        ((Polynomial.natDegree_smul_le _ _).trans ih))

end StrictEUnit
end
