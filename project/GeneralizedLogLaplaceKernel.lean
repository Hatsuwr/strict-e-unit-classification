import LogMixingModeKernel

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem generalizedLogLaplaceSeries_zero_iff_modes (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (s : LaurentSeries (Polynomial K)) :
    generalizedLogLaplaceSeries rho h s=0 ↔
      ∀ n : ℤ,logMixingMode rho n (s.coeff (n+1))=0 := by
  constructor
  · intro hz n
    have he := congrArg (fun t : LaurentSeries (Polynomial K) => t.coeff n) hz
    dsimp only at he
    rw [generalizedLogLaplaceSeries_coeff,HahnSeries.coeff_zero] at he
    exact (smul_eq_zero.mp he).resolve_left (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro hz
    apply HahnSeries.ext
    funext n
    rw [generalizedLogLaplaceSeries_coeff,hz,smul_zero,HahnSeries.coeff_zero]

/-- The corrected transform's integer-class kernel has ONLY log-free
nonpositive source modes. This is a necessary and sufficient statement. -/
theorem generalizedLogLaplaceSeries_zero_class_kernel (s : LaurentSeries (Polynomial K)) :
    generalizedLogLaplaceSeries 0 logMixing_zero_forward_nonzero s=0 ↔
      (∀ n : ℕ,s.coeff ((n : ℤ)+1)=0) ∧
      (∀ n : ℕ,(s.coeff (-(n : ℤ))).derivative=0) := by
  rw [generalizedLogLaplaceSeries_zero_iff_modes]
  constructor
  · intro h
    constructor
    · intro n
      exact (logMixingForward_eq_zero_iff 0 logMixing_zero_forward_nonzero n _).mp (h n)
    · intro n
      have hi : Int.negSucc n+1= -(n : ℤ) := by omega
      have he := h (Int.negSucc n)
      rw [hi] at he
      exact (logMixingBackward_zero_kernel n _).mp he
  · rintro ⟨hp,hn⟩ k
    cases k with
    | ofNat n => exact (logMixingForward_eq_zero_iff 0 logMixing_zero_forward_nonzero n _).mpr (hp n)
    | negSucc n =>
      have hi : Int.negSucc n+1= -(n : ℤ) := by omega
      rw [hi]
      exact (logMixingBackward_zero_kernel n _).mpr (hn n)

/-- Every nonpositive kernel mode is constant in the logarithm. -/
theorem generalizedLogLaplaceSeries_kernel_logfree (s : LaurentSeries (Polynomial K))
    (hs : generalizedLogLaplaceSeries 0 logMixing_zero_forward_nonzero s=0) (n : ℕ) :
    s.coeff (-(n : ℤ))=Polynomial.C ((s.coeff (-(n : ℤ))).coeff 0) :=
  Polynomial.eq_C_of_derivative_eq_zero (((generalizedLogLaplaceSeries_zero_class_kernel s).mp hs).2 n)

end StrictEUnit
end
