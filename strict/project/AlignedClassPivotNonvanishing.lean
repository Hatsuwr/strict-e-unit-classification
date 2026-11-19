import AllClassNonzeroPivotExtraction

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- After integer-class alignment, equal exponents are harmless: their
boundary factor is choose(n,n)=1. Distinct noninteger classes never collide. -/
theorem alignedClassPrefixFilter_boundary_nonzero {r : ℕ}
    (rho : Fin r → K)
    (halign : ∀ s t,rho s=rho t ∨ ∀ z : ℤ,rho s-rho t≠(z : K))
    (L : ℤ) (m d : ℕ) (s : Fin r) :
    (allClassPrefixFilter rho L m d).eval (rho s+(L : K)+(m : K))≠0 := by
  rw [allClassPrefixFilter,Polynomial.eval_pow]
  apply pow_ne_zero
  rw [fallingCompositeSymbol_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  change Ring.choose (rho s+(L : K)-(rho t+(L : K))+(m : K)) m≠0
  rw [show rho s+(L : K)-(rho t+(L : K))=rho s-rho t by ring]
  rcases halign s t with he|hne
  · simp [he,Ring.choose_natCast]
  · exact diagonal_choose_nonzero_of_noninteger _ hne m

/-- Full prefix arithmetic follows for an ALREADY aligned actual frame.
Alignment is an explicit hypothesis, not assumed for the constructed frame. -/
theorem alignedLogFrame_common_denominators {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hC : RegularEulerPrefixArithmetic C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (halign : ∀ s t,rho s=rho t ∨ ∀ z : ℤ,rho s-rho t≠(z : K))
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0) :
    ∃ L : ℤ,∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,
      0<D ∧ (D : ℝ)≤E^(N+1) ∧ ∀ m,m≤N →∀ s i t,
      IsIntegral ℤ ((D : K)*((Y i s).coeff t).coeff ((m : ℤ)+L)) := by
  obtain ⟨L,d,E,hE,h⟩ := logFrame_nonzero_pivot_common_denominators C hC rho hrho Y hY hdet
  refine ⟨L,E,hE,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := h N
  exact ⟨D,hD,hDb,fun m hm s => hDi m hm s
    (alignedClassPrefixFilter_boundary_nonzero rho halign L m d s)⟩

end StrictEUnit
end
