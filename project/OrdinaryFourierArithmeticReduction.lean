import OrdinaryFourierSourceResidual
import OrdinaryBorelReflection
import FallingSymbolIntegralDilations

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The SAME integer (or scalar) clears a signed coefficient exactly when it
clears the unsigned coefficient. There is no denominator-growth loss. -/
theorem reciprocal_signed_integral_iff (n : ℕ) (D x : K) :
    IsIntegral ℤ (D*((-1 : K)^n*x)) ↔IsIntegral ℤ (D*x) := by
  have hi : IsIntegral ℤ ((-1 : K)^n) := by
    simpa only [Nat.cast_one] using (ordinaryJet_natCast_integral (K:=K) 1).neg.pow n
  have hs : (-1 : K)^n*(-1 : K)^n=1 := by rw [← mul_pow];simp
  constructor
  · intro h
    convert h.mul hi using 1
    linear_combination -(D*x)*hs
  · intro h
    convert h.mul hi using 1 <;> ring

/-- Exact denominator transfer, for each prefix witness, between ordinary
source coefficients and factorial-normalized Fourier coefficients. -/
theorem reciprocalSignedBorel_integral_iff (f : PowerSeries K) (D : K) (n : ℕ) :
    IsIntegral ℤ (D*PowerSeries.coeff K n (reciprocalSignedBorel f)) ↔
      IsIntegral ℤ (D*((n.factorial : K)*PowerSeries.coeff K n f)) := by
  rw [reciprocalSignedBorel_coeff,mul_assoc,reciprocal_signed_integral_iff]

/-- Every conjugate norm is unchanged by this sign. -/
theorem reciprocalSignedBorel_conjugate_norm (f : PowerSeries K) (sigma : K →+* ℂ) (n : ℕ) :
    ‖sigma (PowerSeries.coeff K n (reciprocalSignedBorel f))‖=
      ‖sigma ((n.factorial : K)*PowerSeries.coeff K n f)‖ := by
  rw [reciprocalSignedBorel_coeff,map_mul,map_mul,map_pow,map_neg,map_one,norm_mul,
    norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,map_mul,norm_mul]

/-- Full strict coefficient arithmetic is equivalent on the two sides.
This transports arithmetic; it does NOT manufacture it from an ODE. -/
theorem reciprocalSignedBorel_strictArithmetic_iff
    (f : PowerSeries AlgebraicComplex) :
    HasStrictEArithmetic (fun n =>PowerSeries.coeff AlgebraicComplex n (reciprocalSignedBorel f)) ↔
      HasStrictEArithmetic (fun n =>(n.factorial : AlgebraicComplex)*PowerSeries.coeff AlgebraicComplex n f) := by
  have hs (n : ℕ) : (-1 : AlgebraicComplex)^n*(-1 : AlgebraicComplex)^n=1 := by
    rw [← mul_pow];simp
  constructor
  · intro h
    have hi := strictEArithmetic_signed_coefficients h
    convert hi using 1
    funext n
    rw [reciprocalSignedBorel_coeff]
    linear_combination -((n.factorial : AlgebraicComplex)*PowerSeries.coeff AlgebraicComplex n f)*hs n
  · intro h
    have hi := strictEArithmetic_signed_coefficients h
    simpa only [reciprocalSignedBorel_coeff,mul_assoc] using hi

/-- Exact arithmetic reduction for the ordinary, log-free Fourier branch:
its canonical inverse solves the ORIGINAL source equation with a derived
finite polynomial forcing term. No all-solutions arithmetic is assumed. -/
theorem reciprocalFourier_ordinary_arithmetic_reduction (m : ℕ)
    (q : Fin (m+1) → Polynomial AlgebraicComplex) (f : PowerSeries AlgebraicComplex) :
    (reciprocalFourierPowerSeriesAction m q f=0 ∧
      HasStrictEArithmetic (fun n =>(n.factorial : AlgebraicComplex)*PowerSeries.coeff AlgebraicComplex n f)) ↔
    (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f)=
        (PowerSeries.trunc (reciprocalCommonDegree m q+1)
          (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f)) : PowerSeries AlgebraicComplex) ∧
      HasStrictEArithmetic (fun n =>PowerSeries.coeff AlgebraicComplex n (reciprocalSignedBorel f))) := by
  rw [reciprocalFourier_zero_iff_source_truncation,reciprocalSignedBorel_strictArithmetic_iff]

end StrictEUnit
end
