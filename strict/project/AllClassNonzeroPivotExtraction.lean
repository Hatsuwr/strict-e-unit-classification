import RegularEulerFieldTransport
import AllClassDiagonalNormalization
import LogFrameFilteredDenominators

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Actual Laurent/log coefficients, not just formal inverse pivots, have
shared exponential denominators wherever the all-class boundary pivot is
nonzero. Collision indices are explicitly excluded from this conclusion. -/
theorem logFrame_nonzero_pivot_common_denominators {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hC : RegularEulerPrefixArithmetic C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0) :
    ∃ L : ℤ,∃ d : ℕ,∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,
      0<D ∧ (D : ℝ)≤E^(N+1) ∧ ∀ m,m≤N →∀ s,
      (allClassPrefixFilter rho L m d).eval (rho s+(L : K)+(m : K))≠0 →
      ∀ i t,IsIntegral ℤ ((D : K)*((Y i s).coeff t).coeff ((m : ℤ)+L)) := by
  obtain ⟨L,d,hYlow,hYdeg⟩ := logFrame_exists_uniform_bounds Y
  obtain ⟨J,W,hJ,_,hJlow⟩ := logFrame_exists_inverse_with_fixed_pole_bound C rho Y hY hdet
  obtain ⟨B,hB,hden⟩ := hC
  obtain ⟨A,hA,hfiltered⟩ := allClassPrefixFilter_filtered_solution_common_denominators
    C B hB hden rho hrho Y J hY hJ L (W : ℤ) d hYlow hYdeg hJlow
  obtain ⟨F,hF,hnormal⟩ := allClassPrefixFilter_shared_log_normalization rho hrho L d
  refine ⟨L,d,F*A,one_le_mul_of_one_le_of_one_le hF hA,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hfiltered N
  obtain ⟨e,he,heb,hei⟩ := hnormal N
  refine ⟨e*D,Nat.mul_pos he hD,?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    exact mul_le_mul heb hDb (Nat.cast_nonneg _) (pow_nonneg (le_trans zero_le_one hF) _)
  · intro m hm s hp i t
    have hs : rho s+(((m : ℤ)+L : ℤ) : K)=rho s+(L : K)+(m : K) := by
      push_cast;ring
    have h := hei s m hm hp (D : K)
      ((logPolynomialToCoefficientSeries (Y i s)).coeff ((m : ℤ)+L))
      (hYdeg i s _) (by
        intro j
        simpa only [literalLogPolynomialFilter_double_coefficient,hs] using hDi m hm s i j) t
    simpa only [Nat.cast_mul,logPolynomialToCoefficientSeries_double_coeff] using h

end StrictEUnit
end
