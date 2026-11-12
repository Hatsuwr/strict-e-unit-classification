import FourierFiniteTwistedAmplitudes
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Independence within each actual exponent block

Extracting the coefficient of Laurent exponent zero recovers the prescribed
polynomial seed. Consequently independent seeds yield independent amplitudes,
without claiming linearity of the chosen recurrence construction. Applied to
one indicial-root block, the seeds are distinct powers of the logarithm.

The scalar field is K, not LaurentSeries K. Different exponent blocks are NOT
combined here: their external powers have not been represented. This module
asserts neither a full represented Fourier basis nor rational exponents,
arithmetic amplitude coefficients, or convergence.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The original seed is recovered by taking Laurent exponent zero. -/
theorem polynomialLogFrobeniusAmplitude_seed_coeff
    (B : ℕ → Polynomial K) (rho : K) (u : Polynomial K) (k : ℕ) :
    ((polynomialLogFrobeniusAmplitude B rho u).coeff k).coeff 0 = u.coeff k := by
  simpa only [polynomialLogFrobeniusCoefficient_zero] using
    polynomialLogFrobeniusAmplitude_coeff B rho u k 0

/-- Independent seeds imply K-linear independence of the exact constructed
amplitudes. No linearity of the seed-to-amplitude function is assumed. -/
theorem polynomialLogFrobeniusAmplitude_linearIndependent
    {ι : Type*} [Fintype ι] (B : ℕ → Polynomial K)
    (rho : ι → K) (u : ι → Polynomial K) (hu : LinearIndependent K u) :
    LinearIndependent K (fun i => polynomialLogFrobeniusAmplitude B (rho i) (u i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp hu c
  ext k
  have hk := congrArg (fun p : Polynomial (LaurentSeries K) => (p.coeff k).coeff 0) hc
  simpa only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul,
    HahnSeries.coeff_sum, HahnSeries.coeff_smul,
    polynomialLogFrobeniusAmplitude_seed_coeff,
    Polynomial.coeff_zero, HahnSeries.coeff_zero] using hk

omit [CharZero K] in
/-- Distinct logarithmic seed orders are independent. -/
theorem frobenius_distinct_power_seeds_linearIndependent
    {ι : Type*} [Fintype ι] (j : ι → ℕ) (hj : Function.Injective j) :
    LinearIndependent K (fun i => (Polynomial.X : Polynomial K) ^ j i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hk := congrArg (fun p : Polynomial K => p.coeff (j i)) hc
  simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_X_pow, hj.eq_iff] using hk

/-- Every actual repeated-root block is independent over K. The fixed root
is an index of the SAME indicial polynomial, not a chosen new spectrum. -/
theorem sameFourierTwistedAmplitude_rootBlock_linearIndependent
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K)
    (hf : Stage56FiniteFuchs A)
    (rho : {x : K // x ∈ (sameFourierEulerCoefficientSymbols A hf 0).roots.toFinset}) :
    LinearIndependent K (fun j : Fin ((sameFourierEulerCoefficientSymbols A hf 0).rootMultiplicity rho.1) =>
      sameFourierTwistedAmplitude A hf ⟨rho,j⟩) := by
  apply polynomialLogFrobeniusAmplitude_linearIndependent
  exact frobenius_distinct_power_seeds_linearIndependent Fin.val Fin.val_injective

/-- Independence holds in each exponent fiber of ANY exact Fin-nu indexing
of the retained construction. No replacement of hf, e, rho or p is made. -/
theorem sameFourierTwistedAmplitude_indexed_block_linearIndependent
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K)
    (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (ξ : K) : LinearIndependent K (fun j : {j : Fin ν // rho j = ξ} => p j.1) := by
  classical
  have hj : Function.Injective
      (fun j : {j : Fin ν // rho j = ξ} => frobeniusRootSeedOrder _ (e.symm j.1)) := by
    intro i j hij
    apply Subtype.ext
    apply e.symm.injective
    apply frobeniusRootSeedIndex_ext _ _ hij
    exact ((hrho i.1).symm.trans i.2).trans (((hrho j.1).symm.trans j.2).symm)
  simp_rw [hp]
  apply polynomialLogFrobeniusAmplitude_linearIndependent
  exact frobenius_distinct_power_seeds_linearIndependent _ hj

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_seed_coeff
#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_linearIndependent
#print axioms StrictEUnit.frobenius_distinct_power_seeds_linearIndependent
#print axioms StrictEUnit.sameFourierTwistedAmplitude_rootBlock_linearIndependent
#print axioms StrictEUnit.sameFourierTwistedAmplitude_indexed_block_linearIndependent
