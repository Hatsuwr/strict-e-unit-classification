import FractionPolynomialTransfer
import EntireTaylorEmbedding
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
New proof reconstruction, not recovered historical source.

The genuine Taylor embedding of actual entire functions transfers an integral
Laurent-fraction relation to a monic polynomial equation for the corresponding
actual quotient wherever its actual denominator is nonzero.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators

namespace StrictEUnit

/-- Genuine entire Taylor expansion followed by the power-to-Laurent inclusion.
The domain consists of actual entire functions, not arbitrary formal series. -/
def entireLaurentRingHom : entireFunctionAlgebra →+* LaurentSeries ℂ :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp entireTaylorAlgHom.toRingHom

@[simp] theorem entireLaurentRingHom_apply (F : entireFunctionAlgebra) :
    entireLaurentRingHom F =
      HahnSeries.ofPowerSeries ℤ ℂ (entireTaylorAlgHom F) := rfl

theorem entireLaurentRingHom_injective : Function.Injective entireLaurentRingHom :=
  HahnSeries.ofPowerSeries_injective.comp entireTaylorAlgHom_injective

/-- Polynomial compatibility uses the genuine analytic Taylor theorem. -/
@[simp] theorem entireLaurentRingHom_polynomial (P : Polynomial ℂ) :
    entireLaurentRingHom (polynomialEntireAlgHom P) =
      algebraMap (Polynomial ℂ) (LaurentSeries ℂ) P := by
  rw [entireLaurentRingHom_apply, entireTaylorAlgHom_polynomial,
    Polynomial.algebraMap_hahnSeries_apply]

theorem entireLaurentRingHom_comp_polynomial :
    entireLaurentRingHom.comp polynomialEntireAlgHom.toRingHom =
      algebraMap (Polynomial ℂ) (LaurentSeries ℂ) := by
  apply RingHom.ext
  intro P
  exact entireLaurentRingHom_polynomial P

/-- Actual evaluation of a polynomial is the usual polynomial evaluation map. -/
theorem entireEvaluation_comp_polynomial (z : ℂ) :
    (entireEvaluation z).toRingHom.comp polynomialEntireAlgHom.toRingHom =
      Polynomial.evalRingHom z := by
  apply RingHom.ext
  intro P
  rfl

/-- A Laurent polynomial relation gives a global actual entire identity after
clearing the denominator.  The conclusion includes zeros of G. -/
theorem entire_fraction_cleared_relation
    (F G : entireFunctionAlgebra) (hG : G ≠ 0)
    (p : Polynomial (Polynomial ℂ))
    (hp : p.eval₂ (algebraMap (Polynomial ℂ) (LaurentSeries ℂ))
      (entireLaurentRingHom F / entireLaurentRingHom G) = 0) :
    fractionClearedEval p polynomialEntireAlgHom.toRingHom F G = 0 := by
  apply fractionClearedEval_eq_zero_of_injective p polynomialEntireAlgHom.toRingHom
    entireLaurentRingHom entireLaurentRingHom_injective F G hG
  simpa only [entireLaurentRingHom_comp_polynomial] using hp

/-- Pointwise form of the global cleared relation.  No evaluation of a Laurent
series at z occurs in this proof. -/
theorem entire_fraction_cleared_relation_pointwise
    (F G : entireFunctionAlgebra) (hG : G ≠ 0)
    (p : Polynomial (Polynomial ℂ))
    (hp : p.eval₂ (algebraMap (Polynomial ℂ) (LaurentSeries ℂ))
      (entireLaurentRingHom F / entireLaurentRingHom G) = 0)
    (z : ℂ) :
    ∑ i ∈ Finset.range (p.natDegree + 1),
      (p.coeff i).eval z * F.val z ^ i * G.val z ^ (p.natDegree - i) = 0 := by
  have h := congrArg (entireEvaluation z)
    (entire_fraction_cleared_relation F G hG p hp)
  simpa only [fractionClearedEval, map_sum, map_mul, map_pow, map_zero,
    entireEvaluation_apply, polynomialEntireAlgHom_apply] using h

/-- The same polynomial gives the actual quotient equation away from zeros
of the entire denominator. -/
theorem entire_fraction_relation
    (F G : entireFunctionAlgebra) (hG : G ≠ 0)
    (p : Polynomial (Polynomial ℂ))
    (hp : p.eval₂ (algebraMap (Polynomial ℂ) (LaurentSeries ℂ))
      (entireLaurentRingHom F / entireLaurentRingHom G) = 0)
    (z : ℂ) (hz : G.val z ≠ 0) :
    (p.map (Polynomial.evalRingHom z)).eval (F.val z / G.val z) = 0 := by
  have h := eval₂_div_eq_zero_of_fractionClearedEval_eq_zero p
    polynomialEntireAlgHom.toRingHom (entireEvaluation z).toRingHom F G hz
    (entire_fraction_cleared_relation F G hG p hp)
  rw [entireEvaluation_comp_polynomial] at h
  simpa only [Polynomial.eval_map, entireEvaluation_apply] using h

/-- Integrality of the genuine Laurent quotient supplies a monic relation
for the actual complex quotient at every point where G is nonzero. -/
theorem entire_fraction_exists_monic_relation
    (F G : entireFunctionAlgebra) (hG : G ≠ 0)
    (hint : IsIntegral (Polynomial ℂ)
      (entireLaurentRingHom F / entireLaurentRingHom G)) :
    ∃ p : Polynomial (Polynomial ℂ), p.Monic ∧
      ∀ z : ℂ, G.val z ≠ 0 →
        (p.map (Polynomial.evalRingHom z)).eval (F.val z / G.val z) = 0 := by
  obtain ⟨p, hpmonic, hproot⟩ := hint
  exact ⟨p, hpmonic, entire_fraction_relation F G hG p hproot⟩

/-- A polynomial cross-multiplication identity on the actual plane returns a
polynomial identity for the genuine Laurent quotient. -/
theorem entire_fraction_eq_polynomial_of_cross_mul
    (F G : entireFunctionAlgebra) (hG : G ≠ 0) (P : Polynomial ℂ)
    (hP : ∀ z : ℂ, P.eval z * G.val z = F.val z) :
    entireLaurentRingHom F / entireLaurentRingHom G =
      algebraMap (Polynomial ℂ) (LaurentSeries ℂ) P := by
  have hG' : entireLaurentRingHom G ≠ 0 := by
    intro h
    apply hG
    apply entireLaurentRingHom_injective
    simpa only [map_zero] using h
  have hactual : polynomialEntireAlgHom P * G = F := by
    apply Subtype.ext
    funext z
    exact hP z
  apply (div_eq_iff hG').mpr
  have hformal := congrArg entireLaurentRingHom hactual
  simpa only [map_mul, entireLaurentRingHom_polynomial] using hformal.symm

end StrictEUnit
