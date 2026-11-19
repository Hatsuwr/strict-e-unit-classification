import GeneralizedLogLaplaceFiniteKernel

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem shiftedPolynomialDerivative_degree_bound (c : K) (p : Polynomial K) :
    (shiftedPolynomialDerivative c p).natDegree≤p.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _))
      (Polynomial.natDegree_smul_le _ _))

theorem logMixingForward_bounded_preimage (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℕ) (p : Polynomial K) :
    ∃ q : Polynomial K,logMixingForward rho n q=p ∧ q.natDegree≤p.natDegree := by
  induction n generalizing p with
  | zero => exact ⟨p,rfl,le_rfl⟩
  | succ n ih =>
    obtain ⟨q,hq,hdeg⟩ := ih (shiftedPolynomialDerivative (rho+(n+1 : ℕ)) p)
    refine ⟨q,?_,hdeg.trans (shiftedPolynomialDerivative_degree_bound _ _)⟩
    rw [logMixingForward,hq,polynomialShiftInverse_leftInverse _ (h n)]

/-- The negative integer sector requires at most ONE additional log degree,
independent of how far the source Laurent index lies below zero. -/
theorem logMixingBackward_zero_bounded_preimage (n : ℕ) (p : Polynomial K) :
    ∃ q : Polynomial K,logMixingBackward (0 : K) (n+1) q=p ∧ q.natDegree≤p.natDegree+1 := by
  induction n generalizing p with
  | zero => exact ⟨polynomialPrimitive p,by rw [logMixingBackward_zero_first,polynomialPrimitive_rightInverse],
      polynomialPrimitive_natDegree_le p⟩
  | succ n ih =>
    have hc : (0 : K)-(n+1 : ℕ)≠0 := by
      simpa only [zero_sub,neg_ne_zero] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n+1 : ℕ) : K)≠0)
    obtain ⟨q,hq,hdeg⟩ := ih (polynomialShiftInverse ((0 : K)-(n+1 : ℕ)) p)
    refine ⟨q,?_,hdeg.trans (Nat.add_le_add_right (polynomialShiftInverse_natDegree_le _ _) 1)⟩
    rw [logMixingBackward,hq,polynomialShiftInverse_rightInverse _ hc]

theorem logMixingMode_zero_bounded_preimage (n : ℤ) (p : Polynomial K) :
    ∃ q : Polynomial K,logMixingMode (0 : K) n q=p ∧ q.natDegree≤p.natDegree+1 := by
  cases n with
  | ofNat n =>
    obtain ⟨q,hq,hd⟩ := logMixingForward_bounded_preimage 0 logMixing_zero_forward_nonzero n p
    exact ⟨q,hq,hd.trans (Nat.le_succ _)⟩
  | negSucc n => exact logMixingBackward_zero_bounded_preimage n p

end StrictEUnit
end
