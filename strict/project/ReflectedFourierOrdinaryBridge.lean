import ReflectedSourceResidualIdentity
import OrdinaryFourierSourceHomogenization
import OrdinaryFourierArithmeticReduction

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The actual reflected Fourier equation reduces to a finite high-tail
condition on the UNREFLECTED original source action. -/
theorem reciprocal_reflected_fourier_zero_iff_original_tail (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalFourierPowerSeriesAction m (ordinaryReflectionTuple m q) f=0 ↔
      ∀ k,reciprocalCommonDegree m (ordinaryReflectionTuple m q)<k →
        PowerSeries.coeff K k (reciprocalOrdinarySourceAction m q (reciprocalUnsignedBorel f))=0 := by
  rw [reciprocalFourier_zero_iff_source_tail_zero,reciprocalSignedBorel_eq_rescale,
    reciprocalOrdinarySourceAction_reflection]
  simp only [PowerSeries.coeff_rescale,mul_eq_zero,
    pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : K)≠0)),false_or]

theorem reciprocal_reflected_fourier_zero_iff_original_truncation (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalFourierPowerSeriesAction m (ordinaryReflectionTuple m q) f=0 ↔
      reciprocalOrdinarySourceAction m q (reciprocalUnsignedBorel f)=
        (PowerSeries.trunc (reciprocalCommonDegree m (ordinaryReflectionTuple m q)+1)
          (reciprocalOrdinarySourceAction m q (reciprocalUnsignedBorel f)) : PowerSeries K) := by
  rw [reciprocal_reflected_fourier_zero_iff_original_tail]
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

theorem reciprocal_reflected_fourier_zero_iff_original_homogenization (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalFourierPowerSeriesAction m (ordinaryReflectionTuple m q) f=0 ↔
      (PowerSeries.derivative K)^[reciprocalCommonDegree m (ordinaryReflectionTuple m q)+1]
        (reciprocalOrdinarySourceAction m q (reciprocalUnsignedBorel f))=0 := by
  rw [reciprocalSource_iterate_zero_iff_tail,reciprocal_reflected_fourier_zero_iff_original_tail]

def reciprocalUnsignedEGF (G : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n =>PowerSeries.coeff K n G/(n.factorial : K)

theorem reciprocalUnsignedBorel_EGF (G : PowerSeries K) :
    reciprocalUnsignedBorel (reciprocalUnsignedEGF G)=G := by
  ext n
  rw [reciprocalUnsignedBorel_coeff,reciprocalUnsignedEGF,PowerSeries.coeff_mk]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- Precise remaining arithmetic gate on the ordinary, log-free branch.
All ordinary Fourier solutions have strict normalized arithmetic IFF every
ordinary solution of D^(d+1)Q has strict ordinary coefficient arithmetic.
Neither side is asserted true merely because the other is equivalent. -/
theorem reciprocal_reflected_fourier_all_ordinary_arithmetic_iff (m : ℕ)
    (q : Fin (m+1) → Polynomial AlgebraicComplex) :
    (∀ f : PowerSeries AlgebraicComplex,
      reciprocalFourierPowerSeriesAction m (ordinaryReflectionTuple m q) f=0 →
        HasStrictEArithmetic (fun n =>(n.factorial : AlgebraicComplex)*PowerSeries.coeff AlgebraicComplex n f)) ↔
    (∀ G : PowerSeries AlgebraicComplex,
      (PowerSeries.derivative AlgebraicComplex)^[reciprocalCommonDegree m (ordinaryReflectionTuple m q)+1]
        (reciprocalOrdinarySourceAction m q G)=0 →
          HasStrictEArithmetic (fun n =>PowerSeries.coeff AlgebraicComplex n G)) := by
  constructor
  · intro h G hG
    have hf : reciprocalFourierPowerSeriesAction m (ordinaryReflectionTuple m q) (reciprocalUnsignedEGF G)=0 := by
      rw [reciprocal_reflected_fourier_zero_iff_original_homogenization,reciprocalUnsignedBorel_EGF]
      exact hG
    have ha := h (reciprocalUnsignedEGF G) hf
    have he (n : ℕ) : (n.factorial : AlgebraicComplex)*PowerSeries.coeff AlgebraicComplex n
        (reciprocalUnsignedEGF G)=PowerSeries.coeff AlgebraicComplex n G := by
      rw [← reciprocalUnsignedBorel_coeff,reciprocalUnsignedBorel_EGF]
    simpa only [he] using ha
  · intro h f hf
    have hg := (reciprocal_reflected_fourier_zero_iff_original_homogenization m q f).mp hf
    have ha := h (reciprocalUnsignedBorel f) hg
    simpa only [reciprocalUnsignedBorel_coeff] using ha

/-- An explicit first-order example rules out replacing the derived finite
forcing by zero. This is NOT a counterexample to the strict-E theorem. -/
theorem reciprocal_ordinary_fourier_need_not_homogeneous_source :
    let q : Fin 2 → Polynomial K := ![0,1]
    let f := reciprocalSignedEGF (PowerSeries.X : PowerSeries K)
    reciprocalFourierPowerSeriesAction 1 q f=0 ∧
      reciprocalOrdinarySourceAction 1 q (reciprocalSignedBorel f)≠0 := by
  intro q f
  have hres : reciprocalOrdinarySourceAction 1 q (reciprocalSignedBorel f)=1 := by
    dsimp only [f]
    rw [reciprocalSignedBorel_EGF]
    simp [reciprocalOrdinarySourceAction,q,Fin.sum_univ_two,Function.iterate_succ_apply]
  refine ⟨?_,by rw [hres];exact one_ne_zero⟩
  rw [reciprocalFourier_zero_iff_source_tail_zero]
  intro k hk
  rw [hres,PowerSeries.coeff_one,if_neg (by omega)]

end StrictEUnit
end
