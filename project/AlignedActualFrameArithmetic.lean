import IntegerClassShiftedFrame

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Alignment is CONSTRUCTED. Every actual frame with the stated source
connection arithmetic admits integer column shifts with full unfiltered
prefix arithmetic, without excluding any collision indices. -/
theorem actualLogFrame_exists_aligned_arithmetic {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hC : RegularEulerPrefixArithmetic C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0) :
    ∃ rep : Fin r → Fin r,∃ shift : Fin r → ℤ,
      (∀ s,rho s=rho (rep s)+(shift s : K)) ∧
      let Y' := Matrix.of fun i j =>frobeniusIntegerShift (shift j) (Y i j)
      Y'.det≠0 ∧
      (∀ j i,twistedLogPolynomialEuler (rho (rep j)) (Y' i j)=
        ∑ l,logPowerSeriesEmbedding (C i l)*Y' l j) ∧
      ∃ L : ℤ,∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,
        0<D ∧ (D : ℝ)≤E^(N+1) ∧ ∀ m,m≤N →∀ s i t,
        IsIntegral ℤ ((D : K)*((Y' i s).coeff t).coeff ((m : ℤ)+L)) := by
  obtain ⟨rep,shift,hs,halign⟩ := exists_integerClass_aligned_representatives rho
  let Y' := Matrix.of fun i j =>frobeniusIntegerShift (shift j) (Y i j)
  have he := integerShift_logFrame_equation C rho (rho ∘ rep) shift hs Y hY
  have hd := integerShift_logFrame_det_nonzero shift Y hdet
  refine ⟨rep,shift,hs,hd,he,?_⟩
  exact alignedLogFrame_common_denominators C hC (rho ∘ rep) (hrho.comp rep) halign Y' he hd

end StrictEUnit
end
