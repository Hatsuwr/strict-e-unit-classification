import ReciprocalSourceActionIdentity

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Signed factorial transform of an ordinary source power series. -/
def reciprocalSignedEGF (G : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => (-1 : K)^n*PowerSeries.coeff K n G/(n.factorial : K)

/-- Canonical inverse on the ENTIRE ordinary power-series space. -/
def reciprocalSignedBorel (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => (-1 : K)^n*(n.factorial : K)*PowerSeries.coeff K n f

theorem reciprocalSignedEGF_coeff (G : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff K n (reciprocalSignedEGF G)=
      (-1 : K)^n*PowerSeries.coeff K n G/(n.factorial : K) := PowerSeries.coeff_mk _ _

theorem reciprocalSignedBorel_coeff (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff K n (reciprocalSignedBorel f)=
      (-1 : K)^n*(n.factorial : K)*PowerSeries.coeff K n f := PowerSeries.coeff_mk _ _

theorem reciprocalSignedEGF_Borel (f : PowerSeries K) :
    reciprocalSignedEGF (reciprocalSignedBorel f)=f := by
  ext n
  rw [reciprocalSignedEGF_coeff,reciprocalSignedBorel_coeff]
  have hs : (-1 : K)^n*(-1 : K)^n=1 := by rw [← mul_pow];simp
  have hf : (n.factorial : K)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  linear_combination (n.factorial : K)*PowerSeries.coeff K n f*(hs)

theorem reciprocalSignedBorel_EGF (G : PowerSeries K) :
    reciprocalSignedBorel (reciprocalSignedEGF G)=G := by
  ext n
  rw [reciprocalSignedBorel_coeff,reciprocalSignedEGF_coeff]
  have hs : (-1 : K)^n*(-1 : K)^n=1 := by rw [← mul_pow];simp
  have hf : (n.factorial : K)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  linear_combination (n.factorial : K)*PowerSeries.coeff K n G*(hs)

theorem reciprocalSignedEGF_eq_actual_transform (G : PowerSeries K) :
    reciprocalSignedEGF G=signedInverseLaplace
      (reciprocalGaugeW*HahnSeries.ofPowerSeries ℤ K G) := by
  ext n
  rw [reciprocalSignedEGF_coeff,signedInverseLaplace_coeff,reciprocalGaugeW,
    signedLaplace_single_coeff,one_mul,add_sub_cancel_right,HahnSeries.ofPowerSeries_apply_coeff]

end StrictEUnit
end
