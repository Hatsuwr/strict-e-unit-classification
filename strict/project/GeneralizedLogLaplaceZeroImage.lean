import LogMixingModeImage

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Every finite-log Laurent target has a finite-log Laurent preimage in the
integer class. Uniform log degree rises by at most one, not with the pole. -/
theorem generalizedLogLaplaceSeries_zero_bounded_surjective
    (s : LaurentSeries (Polynomial K)) (d : ℕ) (hd : ∀ n,(s.coeff n).natDegree≤d) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceSeries 0 logMixing_zero_forward_nonzero u=s ∧
      (∀ n,(u.coeff n).natDegree≤d+1) ∧
      (∀ n,s.coeff (n-1)=0 →u.coeff n=0) := by
  classical
  let t : LaurentSeries (Polynomial K) := HahnSeries.single (1 : ℤ) (1 : Polynomial K)*s
  have ht (k : ℤ) : t.coeff k=s.coeff (k-1) := by
    have hi : k=(k-1)+1 := by omega
    change (HahnSeries.single (1 : ℤ) (1 : Polynomial K)*s).coeff k=_
    rw [hi,HahnSeries.coeff_single_mul_add,one_mul]
    congr 1
    omega
  have hq (k : ℤ) : ∃ q : Polynomial K,
      logMixingMode (0 : K) (k-1) q=((-1 : K)^(k-1)) • t.coeff k ∧
      q.natDegree≤d+1 ∧ (t.coeff k=0 →q=0) := by
    by_cases hz : t.coeff k=0
    · exact ⟨0,by rw [logMixingMode_zero 0 logMixing_zero_forward_nonzero,hz,smul_zero],
        by simp,fun _ =>rfl⟩
    · obtain ⟨q,hq,hdeg⟩ := logMixingMode_zero_bounded_preimage (k-1)
        (((-1 : K)^(k-1)) • t.coeff k)
      refine ⟨q,hq,hdeg.trans ?_,fun he =>False.elim (hz he)⟩
      apply Nat.add_le_add_right
      exact (Polynomial.natDegree_smul_le _ _).trans (by rw [ht];exact hd _)
  choose q hq hdeg hzero using hq
  let u : LaurentSeries (Polynomial K) :=
    { coeff := q
      isPWO_support' := t.isPWO_support.mono (by
        intro k hk
        change t.coeff k≠0
        intro hz
        exact hk (hzero k hz)) }
  refine ⟨u,?_,hdeg,?_⟩
  · apply HahnSeries.ext
    funext n
    rw [generalizedLogLaplaceSeries_coeff]
    change ((-1 : K)^n) • logMixingMode 0 n (q (n+1))=s.coeff n
    have h := hq (n+1)
    have hi : n+1-1=n := by omega
    rw [hi,ht,hi] at h
    rw [h,← mul_smul,← mul_zpow]
    simp
  · intro n hn
    exact hzero n (by rw [ht];exact hn)

end StrictEUnit
end
