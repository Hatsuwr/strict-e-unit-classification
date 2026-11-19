import ActualFrameSolutionDenominators
import LogSeriesGaugeArithmetic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Every component of an actual same-field solution has full nonnegative
common-prefix arithmetic, not merely an arithmetic tail. -/
theorem actualLogFrame_solution_component_arithmetic {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r →K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0)
    (A : ℤ) (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ s i t,IsIntegral ℤ ((D:K)*((Y i s).coeff t).coeff ((m:ℤ)+A)))
    (xi : K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j) :
    ∀ i,LogSeriesPrefixArithmetic (u i) := by
  obtain ⟨L,E,hE,hd⟩ := actualLogFrame_solution_prefix_denominators C rho Y hY hdet A B hB hden xi u hu
  obtain ⟨F,hF,hf⟩ := logPolynomial_tail_to_prefix (fun i z =>(u i).coeff z) L E hE hd
  intro i
  refine ⟨F,hF,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hf N
  exact ⟨D,hD,hDb,fun m hm t =>hDi m hm i t⟩

/-- Any actual preimage appearing as a gauged solution component inherits
prefix arithmetic. The component identity remains explicit until instantiated
with the source-jet embedding; no hypothetical preimage replaces it. -/
theorem actualLogFrame_reflected_preimage_arithmetic {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r →K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0)
    (A : ℤ) (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ s i t,IsIntegral ℤ ((D:K)*((Y i s).coeff t).coeff ((m:ℤ)+A)))
    (xi : K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j)
    (v : LaurentSeries (Polynomial K)) (i : Fin r) (k g : ℤ)
    (hv : u i=HahnSeries.single k (1:Polynomial K)*
      logLaurentReflection (HahnSeries.single g (1:Polynomial K)*v)) :
    LogSeriesPrefixArithmetic v := by
  have h := actualLogFrame_solution_component_arithmetic C rho Y hY hdet A B hB hden xi u hu i
  rw [hv] at h
  exact logSeriesPrefixArithmetic_undo_reflected_gauge v k g h

end StrictEUnit
end
