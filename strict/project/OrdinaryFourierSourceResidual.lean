import OrdinarySignedBorelEquivalence

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Literal Stage53 Fourier action of the SAME reciprocal array. -/
def reciprocalFourierPowerSeriesAction (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (f : PowerSeries K) : PowerSeries K :=
  ∑ l,(stage53_fourierCoeff (reciprocalSourceArray m (reciprocalCommonDegree m q) q) l :
    PowerSeries K)*(PowerSeries.derivative K)^[l.val] f

/-- The entire Fourier residual is the factorial transform of the source
residual AFTER removing its first d+1 coefficients. This is an identity, not
a premise about a homogeneous source solution. -/
theorem reciprocalFourierPowerSeriesAction_EGF_coeff (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (G : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff K n (reciprocalFourierPowerSeriesAction m q (reciprocalSignedEGF G))=
      (-1 : K)^n*PowerSeries.coeff K (n+reciprocalCommonDegree m q+1)
        (reciprocalOrdinarySourceAction m q G)/(n.factorial : K) := by
  rw [reciprocalFourierPowerSeriesAction,reciprocalSignedEGF_eq_actual_transform,
    ← signedLaplace_sourceAction,reciprocalSourceArray_powerSeries_action_identity,
    signedInverseLaplace_coeff]
  have hp : (reciprocalGaugeZ (K:=K))^(reciprocalCommonDegree m q)=
      HahnSeries.single (-(reciprocalCommonDegree m q : ℤ)) (1 : K) := by
    simp only [reciprocalGaugeZ,HahnSeries.single_pow,one_pow,nsmul_eq_mul,mul_neg,mul_one]
  rw [hp,signedLaplace_single_coeff,one_mul]
  have he : (n : ℤ)+1-(-(reciprocalCommonDegree m q : ℤ))=
      ((n+reciprocalCommonDegree m q+1 : ℕ) : ℤ) := by omega
  rw [he,HahnSeries.ofPowerSeries_apply_coeff]

theorem reciprocalFourierPowerSeriesAction_Borel_coeff (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff K n (reciprocalFourierPowerSeriesAction m q f)=
      (-1 : K)^n*PowerSeries.coeff K (n+reciprocalCommonDegree m q+1)
        (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f))/(n.factorial : K) := by
  have h := reciprocalFourierPowerSeriesAction_EGF_coeff m q (reciprocalSignedBorel f) n
  rwa [reciprocalSignedEGF_Borel] at h

/-- Ordinary Fourier solutions correspond to a FINITE source forcing tail,
not in general to homogeneous solutions of the original source equation. -/
theorem reciprocalFourier_zero_iff_source_tail_zero (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalFourierPowerSeriesAction m q f=0 ↔
      ∀ k,reciprocalCommonDegree m q<k →PowerSeries.coeff K k
        (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f))=0 := by
  constructor
  · intro h k hk
    let n := k-reciprocalCommonDegree m q-1
    have hi : n+reciprocalCommonDegree m q+1=k := by dsimp [n];omega
    have hc := reciprocalFourierPowerSeriesAction_Borel_coeff m q f n
    rw [h,map_zero,hi] at hc
    have hz : (-1 : K)^n*PowerSeries.coeff K k
        (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f))=0 := by
      exact (div_eq_zero_iff.mp hc.symm).resolve_right
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro h
    ext n
    rw [reciprocalFourierPowerSeriesAction_Borel_coeff,h _ (by omega),mul_zero,zero_div,map_zero]

/-- Exact finite polynomial forcing, constructed by truncation; the degree
bound is d, the common ORIGINAL source coefficient degree, not Fourier order. -/
theorem reciprocalFourier_zero_iff_source_truncation (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalFourierPowerSeriesAction m q f=0 ↔
      reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f)=
        (PowerSeries.trunc (reciprocalCommonDegree m q+1)
          (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f)) : PowerSeries K) := by
  rw [reciprocalFourier_zero_iff_source_tail_zero]
  constructor
  · intro h
    ext k
    rw [Polynomial.coeff_coe,PowerSeries.coeff_trunc]
    split_ifs with hk
    · rfl
    · exact h k (by omega)
  · intro h k hk
    have hc := congrArg (PowerSeries.coeff K k) h
    rw [Polynomial.coeff_coe,PowerSeries.coeff_trunc,if_neg (by omega)] at hc
    exact hc

end StrictEUnit
end
