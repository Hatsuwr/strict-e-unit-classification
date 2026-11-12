import LogMixingModeIntertwining

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem polynomialShiftInverse_add (c : K) (hc : c≠0) (p q : Polynomial K) :
    polynomialShiftInverse c (p+q)=polynomialShiftInverse c p+polynomialShiftInverse c q := by
  apply shiftedPolynomialDerivative_injective c hc
  rw [map_add,polynomialShiftInverse_rightInverse c hc,
    polynomialShiftInverse_rightInverse c hc,polynomialShiftInverse_rightInverse c hc]

theorem polynomialShiftInverse_smul (c a : K) (hc : c≠0) (p : Polynomial K) :
    polynomialShiftInverse c (a • p)=a • polynomialShiftInverse c p := by
  apply shiftedPolynomialDerivative_injective c hc
  rw [map_smul,polynomialShiftInverse_rightInverse c hc,polynomialShiftInverse_rightInverse c hc]

theorem logMixingMode_add (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (n : ℤ) (p q : Polynomial K) :
    logMixingMode rho n (p+q)=logMixingMode rho n p+logMixingMode rho n q := by
  cases n with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [logMixingMode] at ih
      simpa only [logMixingMode,logMixingForward,ih] using
        polynomialShiftInverse_add _ (h n) (logMixingForward rho n p) (logMixingForward rho n q)
  | negSucc n =>
    have hb : ∀ k,logMixingBackward rho k (p+q)=logMixingBackward rho k p+logMixingBackward rho k q := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp only [logMixingBackward,ih,map_add]
    exact hb (n+1)

theorem logMixingMode_smul (rho a : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (n : ℤ) (p : Polynomial K) :
    logMixingMode rho n (a • p)=a • logMixingMode rho n p := by
  cases n with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [logMixingMode] at ih
      simpa only [logMixingMode,logMixingForward,ih] using
        polynomialShiftInverse_smul _ a (h n) (logMixingForward rho n p)
  | negSucc n =>
    have hb : ∀ k,logMixingBackward rho k (a • p)=a • logMixingBackward rho k p := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp only [logMixingBackward,ih,map_smul]
    exact hb (n+1)

theorem logMixingMode_zero (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℤ) :
    logMixingMode rho n (0 : Polynomial K)=0 := by
  simpa only [zero_smul] using logMixingMode_smul rho 0 h n (0 : Polynomial K)

end StrictEUnit
end
