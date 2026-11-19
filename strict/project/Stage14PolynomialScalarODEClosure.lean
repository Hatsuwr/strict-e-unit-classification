import Stage14ScalarODEClosure
import Mathlib.RingTheory.Localization.Integer
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Clearing denominators of scalar differential equations

This module clears a common denominator from a finite nonzero scalar tuple,
proves that the resulting polynomial tuple is nonzero, and obtains sum/product
closure for polynomial-coefficient relations in an algebra over k(x). It does
not identify that algebra with entire or meromorphic analytic functions.
-/
noncomputable section
open scoped BigOperators nonZeroDivisors
namespace StrictEUnit

section ClearDenominators
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k R] [Algebra B R]

/-- Finite denominator clearing preserves a genuinely nonzero coefficient tuple.
The coefficients in A act through its injective map to its fraction field B. -/
theorem stage14_clear_differential_denominators
    (A : Type*) [CommRing A] [IsDomain A] [Algebra A B] [IsFractionRing A B]
    (d : Derivation k R R) {f : R}
    (hf : HasScalarLinearDifferentialRelation (B := B) d f) :
    ∃ n : ℕ, ∃ p : Fin (n + 1) → A,
      (∃ i, p i ≠ 0) ∧
        ∑ i, (algebraMap A B (p i)) • ((d : R → R)^[i.val]) f = 0 := by
  obtain ⟨n, c, hne, heq⟩ := hf
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  choose p hp using hb
  have hbne : algebraMap A B (b : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  refine ⟨n, p, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hne
    refine ⟨i, ?_⟩
    intro hpi
    have hzero : algebraMap A B (b : A) * c i = 0 := by
      rw [← Algebra.smul_def, ← hp i, hpi, map_zero]
    exact (mul_ne_zero hbne hi) hzero
  · calc
      ∑ i, (algebraMap A B (p i)) • ((d : R → R)^[i.val]) f =
          ∑ i, (algebraMap A B (b : A) * c i) • ((d : R → R)^[i.val]) f := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hp i, Algebra.smul_def (b : A) (c i)]
      _ = algebraMap A B (b : A) • (∑ i, c i • ((d : R → R)^[i.val]) f) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_smul]
      _ = 0 := by rw [heq, smul_zero]
end ClearDenominators

section PolynomialCoefficients
variable {k R : Type*} [Field k] [CommRing R]
  [Algebra k R] [Algebra (RatFunc k) R] [IsScalarTower k (RatFunc k) R]

/-- A nonzero polynomial tuple acts through the rational-function scalar field.
This is an algebraic relation, not the analytic predicate on functions ℂ → ℂ. -/
def HasPolynomialScalarDifferentialRelation (d : Derivation k R R) (f : R) : Prop :=
  ∃ n : ℕ, ∃ p : Fin (n + 1) → Polynomial k,
    (∃ i, p i ≠ 0) ∧
      ∑ i, (algebraMap (Polynomial k) (RatFunc k) (p i)) •
        ((d : R → R)^[i.val]) f = 0

/-- Scalar equations over k(x) and nonzero polynomial-coefficient equations
are equivalent by an actual common-denominator construction. -/
theorem stage14_polynomialScalarRelation_iff (d : Derivation k R R) (f : R) :
    HasPolynomialScalarDifferentialRelation d f ↔
      HasScalarLinearDifferentialRelation (B := RatFunc k) d f := by
  constructor
  · rintro ⟨n, p, hne, heq⟩
    refine ⟨n, fun i => algebraMap (Polynomial k) (RatFunc k) (p i), ?_, heq⟩
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, fun h => hi (IsFractionRing.to_map_eq_zero_iff.mp h)⟩
  · exact stage14_clear_differential_denominators (Polynomial k) d

/-- Finite stable span produces an actual nonzero polynomial coefficient tuple. -/
theorem finiteDifferentialSpan_polynomialScalarRelation
    (d : Derivation k R R) {f : R}
    (hf : HasFiniteDifferentialSpan (B := RatFunc k) d f) :
    HasPolynomialScalarDifferentialRelation d f :=
  (stage14_polynomialScalarRelation_iff d f).mpr (finiteDifferentialSpan_has_relation d hf)

/-- Polynomial-coefficient scalar relations are closed under addition in an
actual compatible differential algebra over k(x). -/
theorem polynomialScalarDifferentialRelation_add
    (dB : Derivation k (RatFunc k) (RatFunc k)) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap (RatFunc k) R b) =
      algebraMap (RatFunc k) R (dB b)) {f g : R}
    (hf : HasPolynomialScalarDifferentialRelation d f)
    (hg : HasPolynomialScalarDifferentialRelation d g) :
    HasPolynomialScalarDifferentialRelation d (f + g) :=
  (stage14_polynomialScalarRelation_iff d (f + g)).mpr
    (scalarLinearDifferentialRelation_add dB d hcompat
      ((stage14_polynomialScalarRelation_iff d f).mp hf)
      ((stage14_polynomialScalarRelation_iff d g).mp hg))

/-- Polynomial-coefficient scalar relations are closed under multiplication. -/
theorem polynomialScalarDifferentialRelation_mul
    (dB : Derivation k (RatFunc k) (RatFunc k)) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap (RatFunc k) R b) =
      algebraMap (RatFunc k) R (dB b)) {f g : R}
    (hf : HasPolynomialScalarDifferentialRelation d f)
    (hg : HasPolynomialScalarDifferentialRelation d g) :
    HasPolynomialScalarDifferentialRelation d (f * g) :=
  (stage14_polynomialScalarRelation_iff d (f * g)).mpr
    (scalarLinearDifferentialRelation_mul dB d hcompat
      ((stage14_polynomialScalarRelation_iff d f).mp hf)
      ((stage14_polynomialScalarRelation_iff d g).mp hg))
end PolynomialCoefficients
end StrictEUnit
