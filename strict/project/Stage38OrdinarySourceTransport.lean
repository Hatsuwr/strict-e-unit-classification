import Stage38SourceDifferentialTransport
import Stage32FormalToActualFrame

/-!
# The scalar source equation reaches the exact Stage32 ordinary derivation

Source differentiation is t^(-N)D_N on K((t))[ell]. Coefficient extension
sends t^N to the literal ramified arithmetic coordinate in the existing
ambient field. Thus all ordinary iterates, and polynomial scalar equations,
transport with the original coefficient tuple mapped coefficientwise.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The original z-coordinate after positive ramification. -/
def stage38_sourceCoordinate (N : ℕ) : Polynomial (LaurentSeries K) :=
  Polynomial.C (HahnSeries.single (N : ℤ) 1)

/-- Ordinary z differentiation, not an incorrectly rescaled Euler iterate. -/
def stage38_sourceOrdinary (N : ℕ) (p : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  Polynomial.C (HahnSeries.single (-(N : ℤ)) 1) * stage38_sourceEuler N p

@[simp] theorem stage38_sourceOrdinary_apply (N : ℕ)
    (p : Polynomial (LaurentSeries K)) :
    stage38_sourceOrdinary N p =
      Polynomial.C (HahnSeries.single (-(N : ℤ)) 1) * stage38_sourceEuler N p := rfl

/-- Ramification acts on each Laurent monomial by multiplying its exponent. -/
theorem stage38_logRamification_monomial (N : ℕ) (hN : N ≠ 0) (a : ℤ) (c : K) :
    stage38_logRamification N hN (Polynomial.C (HahnSeries.single a c)) =
      Polynomial.C (HahnSeries.single ((N : ℤ) * a) c) := by
  change (Polynomial.C (HahnSeries.single a c)).map
    (stage38_laurentRamification N hN).toRingHom = _
  rw [Polynomial.map_C]
  congr 1
  exact HahnSeries.embDomain_single

/-- Refining a source denominator transports the original coordinate literally. -/
theorem stage38_logRamification_coordinate (N : ℕ) (hN : N ≠ 0) (d : ℕ) :
    stage38_logRamification N hN (stage38_sourceCoordinate (K := K) d) =
      stage38_sourceCoordinate (N * d) := by
  simp only [stage38_sourceCoordinate, stage38_logRamification_monomial, Nat.cast_mul]

/-- Ordinary source differentiation commutes with positive denominator refinement.
No factor N is applied to the logarithmic symbol. -/
theorem stage38_logRamification_ordinary [CharZero K]
    (N : ℕ) (hN : N ≠ 0) (d : ℕ) (p : Polynomial (LaurentSeries K)) :
    stage38_sourceOrdinary (N * d) (stage38_logRamification N hN p) =
      stage38_logRamification N hN (stage38_sourceOrdinary d p) := by
  simp only [stage38_sourceOrdinary_apply, map_mul, stage38_logRamification_monomial,
    stage38_logRamification_sourceEuler, Nat.cast_mul, mul_neg]

/-- The ordinary source operation is additive. -/
theorem stage38_sourceOrdinary_add (N : ℕ) (p q : Polynomial (LaurentSeries K)) :
    stage38_sourceOrdinary N (p + q) =
      stage38_sourceOrdinary N p + stage38_sourceOrdinary N q := by
  simp only [stage38_sourceOrdinary_apply, stage38_sourceEuler_add, mul_add]

/-- The ordinary source operation satisfies the actual Leibniz rule. -/
theorem stage38_sourceOrdinary_mul (N : ℕ) (p q : Polynomial (LaurentSeries K)) :
    stage38_sourceOrdinary N (p * q) =
      p * stage38_sourceOrdinary N q + q * stage38_sourceOrdinary N p := by
  simp only [stage38_sourceOrdinary_apply, stage38_sourceEuler_mul]
  ring

variable (k : Subfield ℂ) (f : K →+* k)

/-- The coefficient-extended formal source coordinate equals the actual
ramified Taylor image used throughout the frame construction. -/
theorem stage38_sourceEmbedding_coordinate (N : ℕ) (hN : N ≠ 0) :
    stage38_sourceEmbedding f (stage38_sourceCoordinate (K := K) N) =
      stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) := by
  change stage38_logAmbient (stage38_logMap f
    (Polynomial.C (HahnSeries.single (N : ℤ) 1))) = _
  rw [stage38_logMap_monomial, map_one]
  change RatFunc.C (HahnSeries.single (N : ℤ) (1 : k)) = _
  rw [stage17_ramifiedEntireFormalAlgHom, AlgHom.comp_apply,
    stage17_arithmeticPowerPullback_coordinate, map_pow,
    stage17_entireFormalAlgHom_apply, stage17_entireLaurent_coordinate, ← map_pow]
  congr 1
  simp only [HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow]

/-- The negative source monomial maps to the inverse of that same coordinate. -/
theorem stage38_sourceEmbedding_inverseCoordinate (N : ℕ) (hN : N ≠ 0) :
    stage38_sourceEmbedding f (Polynomial.C (HahnSeries.single (-(N : ℤ)) (1 : K))) =
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← stage38_sourceEmbedding_coordinate k f N hN, ← map_mul]
  change stage38_sourceEmbedding f
    (Polynomial.C (HahnSeries.single (N : ℤ) 1) *
      Polynomial.C (HahnSeries.single (-(N : ℤ)) 1)) = 1
  rw [← Polynomial.C_mul, HahnSeries.single_mul_single, add_neg_cancel, one_mul]
  change stage38_sourceEmbedding f 1 = 1
  exact map_one _

/-- Source ordinary differentiation commutes with the literal target operator. -/
theorem stage38_sourceEmbedding_ordinary (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial (LaurentSeries K)) :
    stage32_ramifiedOrdinaryDerivation k N hN (stage38_sourceEmbedding f p) =
      stage38_sourceEmbedding f (stage38_sourceOrdinary N p) := by
  change (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))⁻¹ *
    formalAmbientDerivation N hN (stage38_sourceEmbedding f p) = _
  rw [stage38_sourceOrdinary_apply, map_mul,
    stage38_sourceEmbedding_inverseCoordinate k f N hN,
    stage38_sourceEmbedding_differential]

/-- Every ordinary jet is transported by the same map. -/
theorem stage38_sourceEmbedding_ordinary_iterate (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial (LaurentSeries K)) (a : ℕ) :
    (stage32_ramifiedOrdinaryDerivation k N hN :
      RatFunc (LaurentSeries k) → RatFunc (LaurentSeries k))^[a]
        (stage38_sourceEmbedding f p) =
      stage38_sourceEmbedding f
        ((stage38_sourceOrdinary N : Polynomial (LaurentSeries K) →
          Polynomial (LaurentSeries K))^[a] p) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      stage38_sourceEmbedding_ordinary]

/-- Constants commute through source coefficient extension and ambient inclusion. -/
theorem stage38_sourceEmbedding_scalar (c : K) :
    stage38_sourceEmbedding f (algebraMap K (Polynomial (LaurentSeries K)) c) =
      algebraMap k (RatFunc (LaurentSeries k)) (f c) := by
  rw [Polynomial.algebraMap_apply, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
  change stage38_logAmbient (stage38_logMap f (Polynomial.C (HahnSeries.single 0 c))) = _
  rw [stage38_logMap_monomial]
  exact seriesRationalScalar_eq_algebraMap (f c)

/-- The chosen polynomial operator tuple is transported without replacing it. -/
theorem stage38_sourceEmbedding_aeval (N : ℕ) (hN : N ≠ 0) (p : Polynomial K) :
    stage38_sourceEmbedding f (Polynomial.aeval (stage38_sourceCoordinate (K := K) N) p) =
      Polynomial.aeval
        (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) (p.map f) := by
  rw [Polynomial.map_aeval_eq_aeval_map (φ := f) (ψ := stage38_sourceEmbedding f)
    (by ext c; exact (stage38_sourceEmbedding_scalar k f c).symm),
    stage38_sourceEmbedding_coordinate k f N hN]

/-- A scalar source ODE gives the exact Stage33 scalar ODE in the established
ambient, with ordinary derivative iterates and coefficientwise mapped tuple. -/
theorem stage38_sourceEmbedding_ordinary_equation (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (p : Fin (m + 1) → Polynomial K) (y : Polynomial (LaurentSeries K))
    (hy : ∑ j, Polynomial.aeval (stage38_sourceCoordinate (K := K) N) (p j) *
      ((stage38_sourceOrdinary N : Polynomial (LaurentSeries K) →
        Polynomial (LaurentSeries K))^[j.val] y) = 0) :
    ∑ j, Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) ((p j).map f) *
      ((stage32_ramifiedOrdinaryDerivation k N hN : RatFunc (LaurentSeries k) →
        RatFunc (LaurentSeries k))^[j.val] (stage38_sourceEmbedding f y)) = 0 := by
  have h := congrArg (stage38_sourceEmbedding f) hy
  simpa only [map_sum, map_mul, map_zero, stage38_sourceEmbedding_aeval k f N hN,
    stage38_sourceEmbedding_ordinary_iterate k f N hN] using h

end StrictEUnit
