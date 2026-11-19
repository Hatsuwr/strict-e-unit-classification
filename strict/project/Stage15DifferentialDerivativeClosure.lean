import Stage14LaurentPolynomialODEClosure

/-!
# Derivative closure of genuine finite differential spans and scalar ODEs

The derivative stays in the very same finite stable subspace. Consequently
nonzero scalar and polynomial ODEs are produced for the derivative, with
rational denominators cleared by the checked finite-tuple construction.
-/
noncomputable section
namespace StrictEUnit

section General
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k R] [Algebra B R]

/-- The same finite stable subspace contains the derivative. -/
theorem finiteDifferentialSpan_derivative (d : Derivation k R R) {f : R}
    (hf : HasFiniteDifferentialSpan (B := B) d f) :
    HasFiniteDifferentialSpan (B := B) d (d f) := by
  obtain ⟨M, hfg, hstable, hmem⟩ := hf
  exact ⟨M, hfg, hstable, hstable f hmem⟩

variable [Algebra k B] [IsScalarTower k B R]

/-- A genuine scalar ODE implies a nonzero scalar ODE for the derivative. -/
theorem scalarLinearDifferentialRelation_derivative
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) {f : R}
    (hf : HasScalarLinearDifferentialRelation (B := B) d f) :
    HasScalarLinearDifferentialRelation (B := B) d (d f) :=
  finiteDifferentialSpan_has_relation d
    (finiteDifferentialSpan_derivative d
      (scalarLinearDifferentialRelation_finiteSpan dB d hcompat hf))
end General

section Polynomial
variable {k R : Type*} [Field k] [CommRing R]
  [Algebra k R] [Algebra (RatFunc k) R] [IsScalarTower k (RatFunc k) R]

/-- The derivative's polynomial ODE retains a genuinely nonzero coefficient tuple. -/
theorem polynomialScalarDifferentialRelation_derivative
    (dB : Derivation k (RatFunc k) (RatFunc k)) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap (RatFunc k) R b) =
      algebraMap (RatFunc k) R (dB b)) {f : R}
    (hf : HasPolynomialScalarDifferentialRelation d f) :
    HasPolynomialScalarDifferentialRelation d (d f) :=
  (stage14_polynomialScalarRelation_iff d (d f)).mpr
    (scalarLinearDifferentialRelation_derivative dB d hcompat
      ((stage14_polynomialScalarRelation_iff d f).mp hf))
end Polynomial

/-- Concrete derivative ODE closure in the actual Laurent-series differential
field, using its actual compatible rational-function derivative. -/
theorem stage15_laurentPolynomialODE_derivative {k : Type*} [Field k]
    {f : LaurentSeries k}
    (hf : HasPolynomialScalarDifferentialRelation (k := k)
      (stage14_laurentAlgebraDerivation (k := k)) f) :
    HasPolynomialScalarDifferentialRelation (k := k)
      (stage14_laurentAlgebraDerivation (k := k)) (laurentOrdinaryDerivation f) := by
  letI : SMul k (LaurentSeries k) := Algebra.toSMul
  letI : SMul k (RatFunc k) := Algebra.toSMul
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : Module k (RatFunc k) := Algebra.toModule
  letI : IsScalarTower k (RatFunc k) (LaurentSeries k) := stage14_rationalLaurentScalarTower
  exact polynomialScalarDifferentialRelation_derivative (k := k) (R := LaurentSeries k)
    (stage14_rationalOrdinaryDerivation (k := k)) stage14_laurentAlgebraDerivation
    (fun b => stage14_rationalLaurent_differential (k := k) b) hf

end StrictEUnit
