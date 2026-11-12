import PolynomialLogFrobeniusRingEquation

/-!
# A nonzero constructed amplitude at every supplied indicial root

SOURCE-ONLY ADD-ON. No compiler or checker has run on this file. The literal
ring-equation dependency remains uncompiled. The recurrence and first operator
bridge have separately passed their recorded combined checks.

A nonzero seed is retained at Laurent exponent zero. At a supplied root of a
nonzero indicial polynomial, seed 1 therefore gives a nonzero amplitude solving
the literal twisted scalar equation. No exponent z^rho is adjoined. No normalized
ramification, basis, independence, arithmetic, or convergence claim is made.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Retention of the coefficient at Laurent exponent zero prevents the actual
finite-log amplitude from vanishing when its prescribed seed is nonzero. -/
theorem polynomialLogFrobeniusAmplitude_ne_zero
    (B : ℕ → Polynomial K) (rho : K) (u0 : Polynomial K) (hu0 : u0 ≠ 0) :
    polynomialLogFrobeniusAmplitude B rho u0 ≠ 0 := by
  intro hp
  apply hu0
  apply Polynomial.ext
  intro j
  simpa only [hp, Polynomial.coeff_zero, HahnSeries.coeff_zero,
    polynomialLogFrobeniusCoefficient_zero] using
    (polynomialLogFrobeniusAmplitude_coeff B rho u0 j 0).symm

/-- The witness is exactly the amplitude constructed from seed 1, not an
unspecified or possibly zero solution. The root is supplied, not asserted to exist. -/
theorem exists_nonzero_polynomialLogFrobeniusAmplitude_ring_solution
    (r : ℕ) (b : Fin (r + 1) → PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r
      (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (hroot : (scalarEulerCoefficientSymbol r
      (fun i k => PowerSeries.coeff K k (b i)) 0).eval rho = 0) :
    ∃ p : Polynomial (LaurentSeries K),
      p = polynomialLogFrobeniusAmplitude
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)))
        rho (1 : Polynomial K) ∧
      p ≠ 0 ∧
      ∑ i : Fin (r + 1), Polynomial.C (b i : LaurentSeries K) *
        (fun q : Polynomial (LaurentSeries K) =>
          logPolynomialEuler (1 : K) q + rho • q)^[i.val] p = 0 := by
  let B := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))
  refine ⟨polynomialLogFrobeniusAmplitude B rho (1 : Polynomial K), rfl,
    polynomialLogFrobeniusAmplitude_ne_zero B rho 1 one_ne_zero, ?_⟩
  exact polynomialLogFrobeniusAmplitude_ring_equation r b rho 1 hP
    (shiftedPolynomialDifferentialOperator_one_eq_zero_of_root rho (B 0) hP hroot)

end StrictEUnit

#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_ne_zero
#print axioms StrictEUnit.exists_nonzero_polynomialLogFrobeniusAmplitude_ring_solution
