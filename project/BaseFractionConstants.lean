import InjectiveDerivationPullback
import LaurentLogSeriesEmbedding

/-! The manuscript base fraction field has an actual derivation and no
extra constants, proved through the constructed formal-series embedding.
No differential-field extension existence or image-closure is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
namespace StrictEUnit
open Polynomial HahnSeries
variable {k : Type*} [Field k]

/-- Explicit constant in the rational-log target field. -/
def seriesRationalScalar (c : k) : RatFunc (LaurentSeries k) :=
  algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
    (Polynomial.C (single (0:ℤ) c))

/-- The target derivation at the manuscript's precise scale. -/
def scaledSeriesDerivation (N : ℕ) :
    Derivation ℤ (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)) :=
  seriesRationalScalar ((N:k)⁻¹) • logRationalDerivation (N:k)

/-- The actual scaled target derivation agrees with the actual base derivation. -/
theorem scaledSeriesDerivation_base [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (p : LaurentLogBase k) :
    scaledSeriesDerivation (k:=k) N
      (laurentLogFractionToRatFunc (algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k)) p)) =
    laurentLogFractionToRatFunc
      (algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k)) (manuscriptBaseDerivation N p)) := by
  rw [laurentLogFractionToRatFunc_algebraMap, laurentLogFractionToRatFunc_algebraMap]
  change seriesRationalScalar ((N:k)⁻¹) *
    rationalDerivationExtension (K:=LaurentSeries k) (logPolynomialDerivation (N:k))
      (algebraMap _ (RatFunc (LaurentSeries k)) (laurentLogToSeriesPolynomial p)) =
    algebraMap _ (RatFunc (LaurentSeries k))
      (laurentLogToSeriesPolynomial (manuscriptBaseDerivation N p))
  rw [rationalDerivationExtension_algebraMap, logPolynomialDerivation_apply,
    laurentLogToSeriesPolynomial_derivation N hN, map_mul]
  rfl

/-- Closure is proved on every fraction by the explicit quotient-rule preimage. -/
theorem baseFraction_derivative_closed [CharZero k] (N : ℕ) (hN : N ≠ 0) :
    ∀ x : FractionRing (LaurentLogBase k), ∃ y : FractionRing (LaurentLogBase k),
      laurentLogFractionToRatFunc y =
        scaledSeriesDerivation (k:=k) N (laurentLogFractionToRatFunc x) :=
  fraction_image_derivative_closed (R:=LaurentLogBase k)
    (F:=FractionRing (LaurentLogBase k)) (L:=RatFunc (LaurentSeries k))
    laurentLogFractionToRatFunc (scaledSeriesDerivation N)
    (manuscriptBaseDerivation N) (scaledSeriesDerivation_base N hN)

/-- The actual derivation on the base fraction field, constructed rather than assumed. -/
def baseFractionDerivation [CharZero k] (N : ℕ) (hN : N ≠ 0) :
    Derivation ℤ (FractionRing (LaurentLogBase k)) (FractionRing (LaurentLogBase k)) :=
  injectiveDerivationPullback laurentLogFractionToRatFunc laurentLogFractionToRatFunc_injective
    (scaledSeriesDerivation N) (baseFraction_derivative_closed N hN)

@[simp] theorem baseFractionDerivation_embed [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (x : FractionRing (LaurentLogBase k)) :
    laurentLogFractionToRatFunc (baseFractionDerivation (k:=k) N hN x) =
      scaledSeriesDerivation (k:=k) N (laurentLogFractionToRatFunc x) :=
  injectiveDerivationPullback_spec _ _ _ _ x

/-- The constructed fraction derivation really extends the manuscript base derivation. -/
@[simp] theorem baseFractionDerivation_algebraMap [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (p : LaurentLogBase k) :
    baseFractionDerivation (k:=k) N hN
      (algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k)) p) =
    algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k))
      (manuscriptBaseDerivation N p) := by
  apply laurentLogFractionToRatFunc_injective
  rw [baseFractionDerivation_embed]
  exact scaledSeriesDerivation_base N hN p

/-- The actual base fraction-field derivation has exactly the embedded constants k. -/
theorem baseFractionDerivation_constants [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (x : FractionRing (LaurentLogBase k)) :
    baseFractionDerivation (k:=k) N hN x = 0 ↔
      ∃ c : k, x = algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k))
        (Polynomial.C (AddMonoidAlgebra.single (0:ℤ) c)) := by
  have hNk : (N:k) ≠ 0 := by exact_mod_cast hN
  have hc : seriesRationalScalar ((N:k)⁻¹) ≠ 0 := by
    unfold seriesRationalScalar
    apply RatFunc.algebraMap_ne_zero
    intro hh
    have ht := congrArg (fun p : Polynomial (LaurentSeries k) => (p.coeff 0).coeff 0) hh
    have hz : (N:k)⁻¹ = 0 := by
      simpa only [Polynomial.coeff_C_zero, HahnSeries.coeff_single_same,
        Polynomial.coeff_zero, HahnSeries.coeff_zero] using ht
    exact inv_ne_zero hNk hz
  have heq : baseFractionDerivation (k:=k) N hN x = 0 ↔
      scaledSeriesDerivation (k:=k) N (laurentLogFractionToRatFunc x) = 0 := by
    rw [← baseFractionDerivation_embed, ← map_zero laurentLogFractionToRatFunc]
    exact laurentLogFractionToRatFunc_injective.eq_iff.symm
  rw [heq]
  change seriesRationalScalar ((N:k)⁻¹) *
    logRationalDerivation (N:k) (laurentLogFractionToRatFunc x) = 0 ↔ _
  rw [mul_eq_zero]
  simp only [hc, false_or]
  exact embedded_laurentLog_fraction_constants (N:k) hNk x

/-- The explicit constant presentation is the usual scalar algebra map. -/
theorem baseFraction_scalar_eq_algebraMap (c : k) :
    algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k))
      (Polynomial.C (AddMonoidAlgebra.single (0:ℤ) c)) =
    algebraMap k (FractionRing (LaurentLogBase k)) c := by
  rw [IsScalarTower.algebraMap_apply k (LaurentLogBase k) (FractionRing (LaurentLogBase k))]
  rfl

/-- Standard algebra-map formulation of the actual constant-field theorem. -/
theorem baseFractionDerivation_constants_algebraMap [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (x : FractionRing (LaurentLogBase k)) :
    baseFractionDerivation (k:=k) N hN x = 0 ↔
      ∃ c : k, algebraMap k (FractionRing (LaurentLogBase k)) c = x := by
  rw [baseFractionDerivation_constants N hN x]
  simp only [baseFraction_scalar_eq_algebraMap, eq_comm]

end StrictEUnit

#print axioms StrictEUnit.seriesRationalScalar
#print axioms StrictEUnit.scaledSeriesDerivation
#print axioms StrictEUnit.scaledSeriesDerivation_base
#print axioms StrictEUnit.baseFraction_derivative_closed
#print axioms StrictEUnit.baseFractionDerivation
#print axioms StrictEUnit.baseFractionDerivation_embed
#print axioms StrictEUnit.baseFractionDerivation_algebraMap
#print axioms StrictEUnit.baseFractionDerivation_constants
#print axioms StrictEUnit.baseFraction_scalar_eq_algebraMap
#print axioms StrictEUnit.baseFractionDerivation_constants_algebraMap
