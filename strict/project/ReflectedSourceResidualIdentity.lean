import OrdinaryFourierSourceResidual
import OrdinaryBorelReflection

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Full reflection identity, retaining an arbitrary nonzero source residual. -/
theorem reciprocalOrdinarySourceAction_reflection (m : ℕ)
    (p : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalOrdinarySourceAction m (ordinaryReflectionTuple m p)
      (PowerSeries.rescale (-1 : K) f)=
      PowerSeries.rescale (-1 : K) (reciprocalOrdinarySourceAction m p f) := by
  unfold reciprocalOrdinarySourceAction
  have hterm (i : Fin (m + 1)) :
      (ordinaryReflectionTuple m p i : PowerSeries K) *
          (PowerSeries.derivative K)^[i.val] (PowerSeries.rescale (-1 : K) f) =
        PowerSeries.rescale (-1 : K)
          ((p i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] f) := by
    have hpcast : PowerSeries.rescale (-1 : K) (p i : PowerSeries K) =
        ((p i).comp (-Polynomial.X) : PowerSeries K) := by
      simpa only [map_neg, map_one, neg_one_mul] using
        ordinaryBorel_rescale_polynomial (-1 : K) (p i)
    have hsign : (-1 : K) ^ i.val * (-1 : K) ^ i.val = 1 := by
      rw [← mul_pow]
      simp only [neg_mul_neg, one_mul, one_pow]
    rw [ordinaryReflectionTuple, Polynomial.coe_mul, Polynomial.coe_C,
      ordinaryBorel_rescale_iterate_derivative, map_mul, hpcast]
    rw [mul_assoc, ← mul_assoc (PowerSeries.C K ((-1 : K) ^ i.val))
      (PowerSeries.C K ((-1 : K) ^ i.val))
      (PowerSeries.rescale (-1 : K) ((PowerSeries.derivative K)^[i.val] f)),
      ← map_mul, hsign, map_one, one_mul]
  calc
    (∑ i, (ordinaryReflectionTuple m p i : PowerSeries K) *
        (PowerSeries.derivative K)^[i.val] (PowerSeries.rescale (-1 : K) f)) =
        PowerSeries.rescale (-1 : K)
          (∑ i, (p i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] f) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)


/-- Unsigned ordinary Borel coefficients are the desired factorial-normalized
Fourier coefficients, without a class or logarithmic identification. -/
def reciprocalUnsignedBorel (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n =>(n.factorial : K)*PowerSeries.coeff K n f

theorem reciprocalUnsignedBorel_coeff (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff K n (reciprocalUnsignedBorel f)=
      (n.factorial : K)*PowerSeries.coeff K n f := PowerSeries.coeff_mk _ _

theorem reciprocalSignedBorel_eq_rescale (f : PowerSeries K) :
    reciprocalSignedBorel f=PowerSeries.rescale (-1 : K) (reciprocalUnsignedBorel f) := by
  ext n
  rw [reciprocalSignedBorel_coeff,PowerSeries.coeff_rescale,reciprocalUnsignedBorel_coeff]
  ring

/-- The actual reflected reciprocal Fourier residual is the high tail of the
UNREFLECTED original source residual, up to one fixed sign and factorial. -/
theorem reciprocal_reflected_fourier_source_coeff (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) (n : ℕ) :
    let d := reciprocalCommonDegree m (ordinaryReflectionTuple m q)
    PowerSeries.coeff K n (reciprocalFourierPowerSeriesAction m (ordinaryReflectionTuple m q) f)=
      (-1 : K)^(d+1)*PowerSeries.coeff K (n+d+1)
        (reciprocalOrdinarySourceAction m q (reciprocalUnsignedBorel f))/(n.factorial : K) := by
  intro d
  rw [reciprocalFourierPowerSeriesAction_Borel_coeff,reciprocalSignedBorel_eq_rescale,
    reciprocalOrdinarySourceAction_reflection,PowerSeries.coeff_rescale]
  change (-1 : K)^n*((-1 : K)^(n+d+1)*_)/_= _
  have hs : (-1 : K)^n*(-1 : K)^n=1 := by rw [← mul_pow];simp
  have hsign : (-1 : K)^n*(-1 : K)^(n+d+1)=(-1 : K)^(d+1) := by
    rw [show n+d+1=n+(d+1) by omega,pow_add,← mul_assoc,hs,one_mul]
  rw [← mul_assoc,hsign]

end StrictEUnit
end
