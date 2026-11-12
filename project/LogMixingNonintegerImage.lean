import GeneralizedLogLaplaceZeroImage

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem logMixingBackward_noninteger_bounded_preimage (rho : K)
    (h : ∀ z : ℤ,rho≠(z : K)) (n : ℕ) (p : Polynomial K) :
    ∃ q : Polynomial K,logMixingBackward rho n q=p ∧ q.natDegree≤p.natDegree := by
  induction n generalizing p with
  | zero => exact ⟨p,rfl,le_rfl⟩
  | succ n ih =>
    have hc : rho-(n : K)≠0 := sub_ne_zero.mpr (by simpa only [Int.cast_natCast] using h (n : ℤ))
    obtain ⟨q,hq,hdeg⟩ := ih (polynomialShiftInverse (rho-(n : K)) p)
    refine ⟨q,?_,hdeg.trans (polynomialShiftInverse_natDegree_le _ _)⟩
    rw [logMixingBackward,hq,polynomialShiftInverse_rightInverse _ hc]

theorem logMixingMode_noninteger_bounded_preimage (rho : K)
    (h : ∀ z : ℤ,rho≠(z : K)) (n : ℤ) (p : Polynomial K) :
    ∃ q : Polynomial K,logMixingMode rho n q=p ∧ q.natDegree≤p.natDegree := by
  cases n with
  | ofNat n => exact logMixingForward_bounded_preimage rho (logMixing_noninteger_forward_nonzero rho h) n p
  | negSucc n => exact logMixingBackward_noninteger_bounded_preimage rho h (n+1) p

end StrictEUnit
end
