import LogMixingModeOperators
import Mathlib.Tactic.Ring

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

def logMixingMode (rho : K) : ℤ →Polynomial K →Polynomial K
  | Int.ofNat n,p => logMixingForward rho n p
  | Int.negSucc n,p => logMixingBackward rho (n+1) p

/-- A bilateral recurrence valid THROUGH the integer collision. It never
requires invertibility of a backward zero factor. -/
theorem logMixingMode_recurrence (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℤ) (p : Polynomial K) :
    shiftedPolynomialDerivative (rho+(n : K)+1) (logMixingMode rho (n+1) p)=
      logMixingMode rho n p := by
  cases n with
  | ofNat n =>
    simpa only [Int.ofNat_eq_coe,Int.natCast_add,Int.natCast_one,Int.cast_natCast,
      Nat.cast_add,Nat.cast_one,add_assoc] using logMixingForward_recurrence rho n (h n) p
  | negSucc n =>
    cases n with
    | zero => simp [logMixingMode,logMixingBackward,logMixingForward]
    | succ n =>
      have hi : (Int.negSucc (n+1))+1=Int.negSucc n := by omega
      rw [hi]
      change shiftedPolynomialDerivative (rho+(Int.negSucc (n+1) : K)+1)
        (logMixingBackward rho (n+1) p)=logMixingBackward rho (n+2) p
      rw [logMixingBackward]
      congr 1
      push_cast
      ring

theorem logMixingMode_derivative (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℤ) (p : Polynomial K) :
    logMixingMode rho n p.derivative=(logMixingMode rho n p).derivative := by
  cases n with
  | ofNat n => exact logMixingForward_derivative rho h n p
  | negSucc n => exact logMixingBackward_derivative rho (n+1) p

theorem logMixingMode_natDegree_le (rho : K) (n : ℤ) (p : Polynomial K) :
    (logMixingMode rho n p).natDegree≤p.natDegree := by
  cases n with
  | ofNat n => exact logMixingForward_natDegree_le rho n p
  | negSucc n => exact logMixingBackward_natDegree_le rho (n+1) p

end StrictEUnit
end
