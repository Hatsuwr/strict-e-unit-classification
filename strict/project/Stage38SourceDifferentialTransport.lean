import Stage38FormalRamification

/-!
# Differential transport of the scalar source algebra

The source is the actual algebra K((t))[ell], with finite log degree. Its
normalized Euler derivation is constructed, not assumed. Its embedding into
the existing formal ambient field commutes with the exact D_N. Therefore
literal finite scalar differential equations and independence transport.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit
variable {K L ι : Type*} [Field K] [Field L]

/-- The normalized source derivation D_N=(t/N)d/dt+d/dell. -/
def stage38_sourceEuler (N : ℕ) (p : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  Polynomial.C (HahnSeries.single (0 : ℤ) (N : K)⁻¹) * logPolynomialEuler (N : K) p

@[simp] theorem stage38_sourceEuler_apply (N : ℕ)
    (p : Polynomial (LaurentSeries K)) :
    stage38_sourceEuler N p =
      Polynomial.C (HahnSeries.single (0 : ℤ) (N : K)⁻¹) *
        logPolynomialEuler (N : K) p := rfl

/-- The normalized source operation is additive. -/
theorem stage38_sourceEuler_add (N : ℕ) (p q : Polynomial (LaurentSeries K)) :
    stage38_sourceEuler N (p + q) = stage38_sourceEuler N p + stage38_sourceEuler N q := by
  simp only [stage38_sourceEuler_apply, logPolynomialEuler_add, mul_add]

/-- Every source-field scalar is a constant for this actual operator. -/
theorem stage38_sourceEuler_scalar (N : ℕ) (c : K) :
    stage38_sourceEuler N (algebraMap K (Polynomial (LaurentSeries K)) c) = 0 := by
  rw [stage38_sourceEuler_apply, logPolynomialEuler_algebraMap, mul_zero]

/-- The normalized source operation satisfies Leibniz by the proved formal
Euler-log product rule. -/
theorem stage38_sourceEuler_mul (N : ℕ) (p q : Polynomial (LaurentSeries K)) :
    stage38_sourceEuler N (p * q) =
      p * stage38_sourceEuler N q + q * stage38_sourceEuler N p := by
  simp only [stage38_sourceEuler_apply, logPolynomialEuler_mul]
  ring

/-- Coefficient extension maps each literal Laurent monomial and leaves log degree zero. -/
@[simp] theorem stage38_logMap_monomial (f : K →+* L) (n : ℤ) (c : K) :
    stage38_logMap f (Polynomial.C (HahnSeries.single n c)) =
      Polynomial.C (HahnSeries.single n (f c)) := by
  change (Polynomial.C (HahnSeries.single n c)).map (stage38_laurentMap f) = _
  rw [Polynomial.map_C]
  congr 1
  exact HahnSeries.map_single f.toZeroHom

/-- The same normalized differential operator commutes with coefficient extension. -/
theorem stage38_logMap_sourceEuler (f : K →+* L) (N : ℕ)
    (p : Polynomial (LaurentSeries K)) :
    stage38_logMap f (stage38_sourceEuler N p) =
      stage38_sourceEuler N (stage38_logMap f p) := by
  simp only [stage38_sourceEuler_apply, map_mul, stage38_logMap_monomial,
    stage38_logMap_euler, map_inv₀, map_natCast]

/-- The polynomial source embeds into the existing formal ambient differential
field with exactly the manuscript scale, without another logarithmic variable. -/
theorem stage38_logAmbient_differential [CharZero L]
    (N : ℕ) (hN : N ≠ 0) (p : Polynomial (LaurentSeries L)) :
    formalAmbientDerivation N hN (stage38_logAmbient p) =
      stage38_logAmbient (stage38_sourceEuler N p) := by
  change seriesRationalScalar ((N : L)⁻¹) *
    rationalDerivationExtension (logPolynomialDerivation (N : L))
      (algebraMap (Polynomial (LaurentSeries L)) (RatFunc (LaurentSeries L)) p) = _
  rw [rationalDerivationExtension_algebraMap, logPolynomialDerivation_apply,
    stage38_sourceEuler_apply]
  rw [map_mul]
  rfl

/-- Ramification fixes scalar constant polynomials literally. -/
theorem stage38_logRamification_constant (N : ℕ) (hN : N ≠ 0) (c : K) :
    stage38_logRamification N hN (Polynomial.C (HahnSeries.single (0 : ℤ) c)) =
      Polynomial.C (HahnSeries.single (0 : ℤ) c) := by
  have h := (stage38_logRamification (K := K) N hN).commutes c
  simpa only [Polynomial.algebraMap_apply, LaurentSeries.algebraMap_apply,
    HahnSeries.C_apply] using h

/-- Common-denominator refinement preserves the normalized source derivation.
The target denominator is N*d and ell continues to mean log z. -/
theorem stage38_logRamification_sourceEuler [CharZero K]
    (N : ℕ) (hN : N ≠ 0) (d : ℕ) (p : Polynomial (LaurentSeries K)) :
    stage38_sourceEuler (N * d) (stage38_logRamification N hN p) =
      stage38_logRamification N hN (stage38_sourceEuler d p) := by
  simp only [stage38_sourceEuler_apply, Nat.cast_mul,
    stage38_logRamification_euler, map_mul, stage38_logRamification_constant]
  rw [← mul_assoc, ← Polynomial.C_mul, HahnSeries.single_mul_single, zero_add]
  congr 3
  have hNk : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hNk, mul_one]

/-- The actual source-to-ambient coefficient extension. -/
def stage38_sourceEmbedding (f : K →+* L) :
    Polynomial (LaurentSeries K) →+* RatFunc (LaurentSeries L) :=
  (stage38_logAmbient (L := L)).toRingHom.comp (stage38_logMap f)

/-- Differential compatibility for the literal coefficientwise source map. -/
theorem stage38_sourceEmbedding_differential [CharZero L]
    (f : K →+* L) (N : ℕ) (hN : N ≠ 0) (p : Polynomial (LaurentSeries K)) :
    formalAmbientDerivation N hN (stage38_sourceEmbedding f p) =
      stage38_sourceEmbedding f (stage38_sourceEuler N p) := by
  change formalAmbientDerivation N hN (stage38_logAmbient (stage38_logMap f p)) =
    stage38_logAmbient (stage38_logMap f (stage38_sourceEuler N p))
  rw [stage38_logAmbient_differential, stage38_logMap_sourceEuler]

/-- All iterated derivatives use the same transport, not a power of a scalar
factor times an Euler iterate. -/
theorem stage38_sourceEmbedding_iterate [CharZero L]
    (f : K →+* L) (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial (LaurentSeries K)) (a : ℕ) :
    (formalAmbientDerivation N hN : RatFunc (LaurentSeries L) → RatFunc (LaurentSeries L))^[a]
      (stage38_sourceEmbedding f p) =
      stage38_sourceEmbedding f
        ((stage38_sourceEuler N : Polynomial (LaurentSeries K) →
          Polynomial (LaurentSeries K))^[a] p) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      stage38_sourceEmbedding_differential]

/-- Any supplied finite scalar equation transports coefficientwise. This does
not assert the availability of a source equation or a source basis. -/
theorem stage38_sourceEmbedding_equation [CharZero L]
    (f : K →+* L) (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (a : Fin m → Polynomial (LaurentSeries K)) (y : Polynomial (LaurentSeries K))
    (hy : ∑ j, a j *
      ((stage38_sourceEuler N : Polynomial (LaurentSeries K) →
        Polynomial (LaurentSeries K))^[j.val] y) = 0) :
    ∑ j, stage38_sourceEmbedding f (a j) *
      ((formalAmbientDerivation N hN : RatFunc (LaurentSeries L) →
        RatFunc (LaurentSeries L))^[j.val] (stage38_sourceEmbedding f y)) = 0 := by
  simpa only [map_sum, map_mul, map_zero, stage38_sourceEmbedding_iterate] using
    congrArg (stage38_sourceEmbedding f) hy

/-- Independence also reaches the exact ambient field, over its larger constants. -/
theorem stage38_sourceEmbedding_linearIndependent [Algebra K L]
    (v : ι → Polynomial (LaurentSeries K)) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => stage38_sourceEmbedding (algebraMap K L) (v i)) :=
  stage38_logSeries_ambient_linearIndependent v hv

end StrictEUnit
