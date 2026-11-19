import DerivationOverConstants

/-! The actual formal Laurent-series rational field as a k-differential
ambient field for the manuscript base. No analytic realization is asserted. -/
noncomputable section
set_option maxHeartbeats 200000
namespace StrictEUnit
variable {k : Type*} [Field k]

/-- The explicit rational-series scalar is the canonical k-algebra map. -/
theorem seriesRationalScalar_eq_algebraMap (c : k) :
    seriesRationalScalar c = algebraMap k (RatFunc (LaurentSeries k)) c := by
  rw [RatFunc.algebraMap_apply (R := k), map_one, div_one]
  unfold seriesRationalScalar
  congr 1
  change Polynomial.C (HahnSeries.single (0 : ℤ) c) =
    Polynomial.C (algebraMap k (LaurentSeries k) c)
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

/-- The actual scaled rational derivation annihilates the actual k-scalars. -/
theorem scaledSeriesDerivation_scalar [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (c : k) :
    scaledSeriesDerivation (k := k) N (algebraMap k (RatFunc (LaurentSeries k)) c) = 0 := by
  change seriesRationalScalar ((N : k)⁻¹) *
    logRationalDerivation (N : k) (algebraMap k (RatFunc (LaurentSeries k)) c) = 0
  have hc : logRationalDerivation (N : k)
      (algebraMap k (RatFunc (LaurentSeries k)) c) = 0 := by
    apply (logRationalDerivation_constants (N : k) (Nat.cast_ne_zero.mpr hN) _).mpr
    exact ⟨c, (seriesRationalScalar_eq_algebraMap c).symm⟩
  rw [hc, mul_zero]

/-- A genuine k-derivation on the formal ambient field, with the manuscript scale. -/
def formalAmbientDerivation [CharZero k] (N : ℕ) (hN : N ≠ 0) :
    Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)) :=
  derivationOverConstants (k := k) (scaledSeriesDerivation N)
    (scaledSeriesDerivation_scalar N hN)

@[simp] theorem formalAmbientDerivation_apply [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (x : RatFunc (LaurentSeries k)) :
    formalAmbientDerivation N hN x = scaledSeriesDerivation N x := rfl

/-- Its exact constant field, expressed using the ordinary scalar algebra map. -/
theorem formalAmbientDerivation_constants [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (x : RatFunc (LaurentSeries k)) :
    formalAmbientDerivation N hN x = 0 ↔
      ∃ c : k, algebraMap k (RatFunc (LaurentSeries k)) c = x := by
  change seriesRationalScalar ((N : k)⁻¹) * logRationalDerivation (N : k) x = 0 ↔ _
  have hscalar : seriesRationalScalar ((N : k)⁻¹) ≠ 0 := by
    rw [seriesRationalScalar_eq_algebraMap]
    exact (map_ne_zero (algebraMap k (RatFunc (LaurentSeries k)))).mpr
      (inv_ne_zero (Nat.cast_ne_zero.mpr hN))
  rw [mul_eq_zero]
  simp only [hscalar, false_or]
  rw [logRationalDerivation_constants (N : k) (Nat.cast_ne_zero.mpr hN)]
  change (∃ c : k, x = seriesRationalScalar c) ↔ _
  simp only [seriesRationalScalar_eq_algebraMap, eq_comm]

/-- The formal base inclusion is genuinely a k-algebra hom. -/
def formalBaseEmbedding : LaurentLogBase k →ₐ[k] RatFunc (LaurentSeries k) :=
  { laurentLogToRatFunc with
    commutes' := fun c => by
      change laurentLogToRatFunc
        (Polynomial.C (AddMonoidAlgebra.single (0 : ℤ) c)) = _
      rw [← laurentLogFractionToRatFunc_algebraMap, laurentLogFractionToRatFunc_scalar]
      exact seriesRationalScalar_eq_algebraMap c }

theorem formalBaseEmbedding_injective : Function.Injective (formalBaseEmbedding (k := k)) :=
  laurentLogToRatFunc_injective

/-- Literal differential compatibility of this actual embedding. -/
theorem formalBaseEmbedding_differential [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (p : LaurentLogBase k) :
    formalAmbientDerivation N hN (formalBaseEmbedding p) =
      formalBaseEmbedding (manuscriptBaseDerivation N p) := by
  change scaledSeriesDerivation N (laurentLogToRatFunc p) =
    laurentLogToRatFunc (manuscriptBaseDerivation N p)
  simpa only [laurentLogFractionToRatFunc_algebraMap] using
    scaledSeriesDerivation_base N hN p
end StrictEUnit
#print axioms StrictEUnit.seriesRationalScalar_eq_algebraMap
#print axioms StrictEUnit.scaledSeriesDerivation_scalar
#print axioms StrictEUnit.formalAmbientDerivation
#print axioms StrictEUnit.formalAmbientDerivation_apply
#print axioms StrictEUnit.formalAmbientDerivation_constants
#print axioms StrictEUnit.formalBaseEmbedding
#print axioms StrictEUnit.formalBaseEmbedding_injective
#print axioms StrictEUnit.formalBaseEmbedding_differential
