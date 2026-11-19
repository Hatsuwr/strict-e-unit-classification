import V5BroadSeriesRealization

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- An algebraic coefficient map preserves all broad bounds. All operations
on sums in this file are finite or formal, never a map of complex limits. -/
theorem v5_broad_algebraic_arithmetic_map
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (ha : V5BroadAlgebraicArithmetic a) :
    V5BroadAlgebraicArithmetic (fun n => σ (a n)) := by
  intro ε hε
  obtain ⟨C,hC,d,hd,hdb,hconj,hint⟩ := ha ε hε
  let v := (algebraicClosure ℚ ℂ).val
  refine ⟨C,hC,d,hd,hdb,?_,?_⟩
  · intro τ n
    exact hconj (τ.comp σ) n
  · intro L n hn
    have hi : IsIntegral ℤ ((d L : AlgebraicComplex) * a n) := by
      apply (isIntegral_algHom_iff (v.restrictScalars ℤ) v.injective).mp
      simpa only [map_mul,map_natCast] using hint L n hn
    have hm := IsIntegral.map ((v.comp σ).restrictScalars ℤ) hi
    simpa only [map_mul,map_natCast,AlgHom.comp_apply] using hm

theorem v5_factorial_series_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a : ℕ → K) :
    PowerSeries.map φ (PowerSeries.mk (fun n => a n / (n.factorial : K))) =
      PowerSeries.mk (fun n => φ (a n) / (n.factorial : L)) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk,map_div₀,map_natCast]

/-- Actual coefficient conjugates are broad entire functions, obtained from
their own sums. The original equation's exact polynomial tuple is conjugated. -/
theorem v5_actual_broad_coefficient_conjugate
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex)
    (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex) (hdf : Differentiable ℂ f)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f) (ha : V5BroadAlgebraicArithmetic a) :
    V5IsBroadEFunction (exponentialGeneratingFunction (fun n => (σ (a n) : ℂ))) := by
  obtain ⟨m,p,⟨i,hi⟩,hode⟩ := hODE
  have hf := (v5_actual_broad_ode_data ⟨f,hdf⟩ a hs m p hode).2
  apply v5_broad_series_realization _ (v5_broad_algebraic_arithmetic_map σ a ha)
    m (fun j => (p j).map σ.toRingHom) ⟨i,(Polynomial.map_ne_zero_iff σ.injective).mpr hi⟩
  have hc := congrArg (PowerSeries.map σ.toRingHom) hf
  rw [map_sum,map_zero] at hc
  simpa only [map_mul,ordinaryBorel_map_iterate_derivative,← Polynomial.polynomial_map_coe,
    v5_factorial_series_map] using hc

#print axioms v5_broad_algebraic_arithmetic_map
#print axioms v5_factorial_series_map
#print axioms v5_actual_broad_coefficient_conjugate
end StrictEUnit
end
