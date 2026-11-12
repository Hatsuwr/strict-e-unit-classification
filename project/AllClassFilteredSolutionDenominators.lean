import AllClassSharedFilterArithmetic
import LogFiniteJetCommonDenominator

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Conditional singular arithmetic bridge with its remaining geometric
obligation exposed: a complete actual solution matrix and a right inverse
IN polynomial-valued Laurent series with a fixed lower-support bound.
Given those objects, filtered-solution arithmetic is PROVED from the same
connection arithmetic and a finite jet, not supplied as a desired premise.
This is not yet arithmetic of the unfiltered solutions. -/
theorem allClassPrefixFilter_filtered_solution_common_denominators {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ) (hB : 1≤B)
    (hden : ∀ M : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(M+1) ∧
      ∀ m,m≤M →∀ l,l≤M →∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (J : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j)
    (hJ : (Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j)))*J=1)
    (L W : ℤ) (d : ℕ)
    (hYlow : ∀ i j a,a<L →(logPolynomialToCoefficientSeries (Y i j)).coeff a=0)
    (hYdeg : ∀ i j a,((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree≤d)
    (hJlow : ∀ i j a,a< -W →(J i j).coeff a=0) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ s i t,IsIntegral ℤ ((D : K)*
        ((literalLogPolynomialFilter (rho s) (allClassPrefixFilter rho L m d) (Y i s)).coeff t).coeff ((m : ℤ)+L)) := by
  obtain ⟨e,he,hei⟩ := logSolution_fixed_jet_common_denominator Y L W d hYlow hYdeg
  obtain ⟨E,hE,hED⟩ := allClassPrefixFilter_shared_connection_denominators C B hB hden rho hrho L d
  have he1 : (1 : ℝ)≤e := by exact_mod_cast he
  refine ⟨E*(e : ℝ),one_le_mul_of_one_le_of_one_le hE he1,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hED N
  refine ⟨D*e,Nat.mul_pos hD he,?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    apply mul_le_mul hDb ?_ (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
    calc
      (e : ℝ)=(e : ℝ)^1 := by rw [pow_one]
      _ ≤ (e : ℝ)^(N+1) := pow_le_pow_right₀ he1 (by omega)
  · intro m hm s i t
    have h := allClassPrefixFilter_solution_finite_jet_integral C rho Y J hY hJ L W d
      hYlow hYdeg hJlow s m (D : K) (e : K)
      (fun i j k hk =>hDi m hm k (hk.trans hm) i j)
      (fun j t k hk =>hei j s t k hk) i t
    simpa only [Nat.cast_mul] using h

end StrictEUnit
end
