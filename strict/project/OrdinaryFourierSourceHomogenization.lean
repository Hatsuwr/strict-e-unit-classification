import OrdinaryFourierSourceResidual
import Stage26ODERecurrenceCoefficients

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Exact derivative characterization of a finite source forcing polynomial. -/
theorem reciprocalSource_iterate_zero_iff_tail (G : PowerSeries K) (d : ℕ) :
    (PowerSeries.derivative K)^[d+1] G=0 ↔
      ∀ k,d<k →PowerSeries.coeff K k G=0 := by
  constructor
  · intro h k hk
    let n := k-d-1
    have hi : n+(d+1)=k := by dsimp [n];omega
    have hc := stage26_coeff_iterate_derivative_asc G (d+1) n
    rw [h,map_zero,hi] at hc
    have hn : (ascPochhammer K (d+1)).eval ((n : K)+1)≠0 := by
      rw [← Nat.cast_add_one,ascPochhammer_nat_eq_natCast_ascFactorial]
      exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.ascFactorial_pos n (d+1)))
    exact (mul_eq_zero.mp hc.symm).resolve_right hn
  · intro h
    ext n
    rw [stage26_coeff_iterate_derivative_asc,h _ (by omega),zero_mul,map_zero]

/-- True homogeneous source replacement for the ordinary Fourier branch:
D^(d+1) composed with the original source action, not that source action alone. -/
theorem reciprocalFourier_zero_iff_homogenized_source (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (f : PowerSeries K) :
    reciprocalFourierPowerSeriesAction m q f=0 ↔
      (PowerSeries.derivative K)^[reciprocalCommonDegree m q+1]
        (reciprocalOrdinarySourceAction m q (reciprocalSignedBorel f))=0 := by
  rw [reciprocalSource_iterate_zero_iff_tail,reciprocalFourier_zero_iff_source_tail_zero]

end StrictEUnit
end
