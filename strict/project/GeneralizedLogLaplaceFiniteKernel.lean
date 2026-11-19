import GeneralizedLogLaplaceKernel
import SignedInverseLaplaceKernelConverse

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The full integer-class kernel is a finite LOG-FREE polynomial in w^-1.
The polynomial is constructed from actual Laurent support, not postulated. -/
theorem generalizedLogLaplaceSeries_kernel_finite_polynomial
    (s : LaurentSeries (Polynomial K))
    (hs : generalizedLogLaplaceSeries 0 logMixing_zero_forward_nonzero s=0) :
    ∃ P : Polynomial K,∀ k : ℤ,s.coeff k=
      if k≤0 then Polynomial.C (P.coeff (-k).toNat) else 0 := by
  let y : LaurentSeries K := s.map (Polynomial.lcoeff K 0)
  have hp := ((generalizedLogLaplaceSeries_zero_class_kernel s).mp hs).1
  have hy : signedInverseLaplace y=0 := by
    apply (signedInverseLaplace_eq_zero_iff y).mpr
    intro n
    change (s.coeff ((n : ℤ)+1)).coeff 0=0
    rw [hp n,Polynomial.coeff_zero]
  have hr := signedInverseLaplace_kernel_reconstruct y hy
  refine ⟨signedLaplaceKernelPolynomial y,?_⟩
  intro k
  by_cases hk : k≤0
  · rw [if_pos hk]
    have hi : -(((-k).toNat : ℕ) : ℤ)=k := by omega
    have hc := generalizedLogLaplaceSeries_kernel_logfree s hs (-k).toNat
    rw [hi] at hc
    rw [hc]
    congr 1
    have he := congrArg (fun u : LaurentSeries K =>u.coeff k) hr
    change (s.coeff k).coeff 0=(signedLaplacePolynomialInZ (signedLaplaceKernelPolynomial y)).coeff k at he
    rw [signedLaplacePolynomialInZ_coeff,if_pos hk] at he
    exact he
  · rw [if_neg hk]
    have hi : (((k-1).toNat : ℕ) : ℤ)+1=k := by omega
    simpa only [hi] using hp (k-1).toNat

/-- No kernel exists in a noninteger exponent class. -/
theorem generalizedLogLaplaceSeries_noninteger_kernel (rho : K)
    (h : ∀ z : ℤ,rho≠(z : K)) (s : LaurentSeries (Polynomial K)) :
    generalizedLogLaplaceSeries rho (logMixing_noninteger_forward_nonzero rho h) s=0 ↔ s=0 := by
  rw [generalizedLogLaplaceSeries_zero_iff_modes]
  have hm : ∀ n : ℤ,∀ p : Polynomial K,logMixingMode rho n p=0 ↔ p=0 := by
    intro n p
    cases n with
    | ofNat n => exact logMixingForward_eq_zero_iff rho (logMixing_noninteger_forward_nonzero rho h) n p
    | negSucc n => exact logMixingBackward_noninteger_kernel rho h (n+1) p
  constructor
  · intro hz
    apply HahnSeries.ext
    funext k
    have he := (hm (k-1) _).mp (hz (k-1))
    simpa only [sub_add_cancel,HahnSeries.coeff_zero] using he
  · rintro rfl n
    exact (hm n _).mpr (HahnSeries.coeff_zero)

end StrictEUnit
end
