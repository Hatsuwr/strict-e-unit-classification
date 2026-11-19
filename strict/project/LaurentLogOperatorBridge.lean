import FiniteLogLaurentTranspose
import ShiftedPolynomialDerivative
import Mathlib.Tactic.Abel

/-!
# A literal ring embedding for finite logarithmic Laurent series

SOURCE-ONLY DRAFT. No Lean compiler or checker has been run on this file.
The intended dependency is the checked_r0002 FiniteLogLaurentTranspose source.

The polynomial logarithm is embedded in polynomial-valued Laurent series by
an actual ring homomorphism. Double coefficients prove injectivity. The actual
unnormalized Euler-plus-log operator, shifted by rho, is intertwined with the
coefficient operation D_L + rho + n. No exponent z^rho is adjoined or asserted
to belong to either ring. No normalized, ramified, basis, or arithmetic result
is claimed.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Map Laurent coefficients to constant polynomials, preserving multiplication. -/
def logLaurentCoefficientMap :
    LaurentSeries K →+* LaurentSeries (Polynomial K) where
  toFun s := s.map (Polynomial.C : K →+* Polynomial K)
  map_zero' := by
    apply HahnSeries.ext
    funext n
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_zero, map_zero]
  map_one' := by
    exact HahnSeries.map_one
      (Polynomial.C : K →+* Polynomial K).toMonoidWithZeroHom
  map_add' s t := by
    exact HahnSeries.map_add
      (Polynomial.C : K →+* Polynomial K).toAddMonoidHom
  map_mul' s t := by
    exact HahnSeries.map_mul
      (Polynomial.C : K →+* Polynomial K).toNonUnitalRingHom

@[simp] theorem logLaurentCoefficientMap_coeff (s : LaurentSeries K) (n : ℤ) :
    (logLaurentCoefficientMap s).coeff n = Polynomial.C (s.coeff n) := rfl

/-- The formal log variable maps to the constant Laurent series with value X. -/
def logPolynomialToCoefficientSeries :
    Polynomial (LaurentSeries K) →+* LaurentSeries (Polynomial K) :=
  Polynomial.eval₂RingHom logLaurentCoefficientMap
    (HahnSeries.C (Polynomial.X : Polynomial K))

@[simp] theorem logPolynomialToCoefficientSeries_C (s : LaurentSeries K) :
    logPolynomialToCoefficientSeries (Polynomial.C s) =
      logLaurentCoefficientMap s := by
  change Polynomial.eval₂ logLaurentCoefficientMap
    (HahnSeries.C (Polynomial.X : Polynomial K)) (Polynomial.C s) = _
  exact Polynomial.eval₂_C _ _

/-- Monomials require only multiplication by a constant Laurent series. -/
theorem logPolynomialToCoefficientSeries_monomial_coeff
    (j : ℕ) (s : LaurentSeries K) (n : ℤ) :
    (logPolynomialToCoefficientSeries (Polynomial.monomial j s)).coeff n =
      Polynomial.monomial j (s.coeff n) := by
  change (Polynomial.eval₂ logLaurentCoefficientMap
    (HahnSeries.C (Polynomial.X : Polynomial K))
      (Polynomial.monomial j s)).coeff n = _
  rw [Polynomial.eval₂_monomial]
  have hpow :
      (HahnSeries.C (Polynomial.X : Polynomial K) :
        LaurentSeries (Polynomial K)) ^ j =
      HahnSeries.C ((Polynomial.X : Polynomial K) ^ j) :=
    (map_pow (HahnSeries.C : Polynomial K →+* LaurentSeries (Polynomial K))
      Polynomial.X j).symm
  rw [hpow, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    logLaurentCoefficientMap_coeff]
  exact Polynomial.C_mul_X_pow_eq_monomial

/-- Every integer Laurent exponent and every log coefficient are preserved. -/
theorem logPolynomialToCoefficientSeries_double_coeff
    (p : Polynomial (LaurentSeries K)) (n : ℤ) (j : ℕ) :
    ((logPolynomialToCoefficientSeries p).coeff n).coeff j =
      (p.coeff j).coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, HahnSeries.coeff_add, Polynomial.coeff_add, hp, hq]
  | monomial k s =>
    rw [logPolynomialToCoefficientSeries_monomial_coeff]
    simp only [Polynomial.coeff_monomial]
    split_ifs <;> rfl

theorem logPolynomialToCoefficientSeries_injective :
    Function.Injective (logPolynomialToCoefficientSeries (K := K)) := by
  intro p q hpq
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  have h := congrArg (fun s : LaurentSeries (Polynomial K) => (s.coeff n).coeff j) hpq
  simpa only [logPolynomialToCoefficientSeries_double_coeff] using h

/-- Scalar compatibility is proved from literal coefficients. -/
theorem logPolynomialToCoefficientSeries_smul
    (c : K) (p : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (c • p) =
      c • logPolynomialToCoefficientSeries p := by
  apply HahnSeries.ext
  funext n
  apply Polynomial.ext
  intro j
  simp only [logPolynomialToCoefficientSeries_double_coeff,
    Polynomial.coeff_smul, HahnSeries.coeff_smul]
  change (algebraMap K (LaurentSeries K) c * p.coeff j).coeff n =
    c * (p.coeff j).coeff n
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul]

/-- The checked bounded-log transpose is a right inverse on its exact domain. -/
theorem logPolynomialToCoefficientSeries_finiteLogLaurentTranspose
    (d : ℕ) (s : LaurentSeries (Polynomial K)) (hs : HasUniformLogBound s d) :
    logPolynomialToCoefficientSeries (finiteLogLaurentTranspose d s) = s := by
  apply HahnSeries.ext
  funext n
  apply Polynomial.ext
  intro j
  rw [logPolynomialToCoefficientSeries_double_coeff,
    finiteLogLaurentTranspose_double_coeff d s hs]

/-- In particular, a bounded coefficient sequence is represented exactly,
not merely at its nonnegative Laurent coefficients. -/
theorem logPolynomialToCoefficientSeries_transpose_powerSeries_mk
    (u : ℕ → Polynomial K) (d : ℕ)
    (hu : ∀ n j, d ≤ j → (u n).coeff j = 0) :
    logPolynomialToCoefficientSeries
      (finiteLogLaurentTranspose d
        ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
          LaurentSeries (Polynomial K))) =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K)) :=
  logPolynomialToCoefficientSeries_finiteLogLaurentTranspose d _
    (uniformLogBound_powerSeries_mk u d hu)

/-- Exact power-series representation explicitly excludes negative Laurent terms. -/
theorem logPolynomial_negative_coeff_of_powerSeries
    (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K)))
    (n : ℤ) (hn : n < 0) (j : ℕ) :
    (p.coeff j).coeff n = 0 := by
  rw [← logPolynomialToCoefficientSeries_double_coeff p n j,
    hp, PowerSeries.coeff_coe, if_pos hn]
  exact Polynomial.coeff_zero j

/-- The universal differential identity, with no support or degree assumption
on p beyond its membership in the actual polynomial-log ring. -/
theorem logPolynomialToCoefficientSeries_euler
    (N : K) (p : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (logPolynomialEuler N p) =
      polynomialCoefficientEuler N (logPolynomialToCoefficientSeries p) := by
  apply HahnSeries.ext
  funext n
  apply Polynomial.ext
  intro j
  change ((logPolynomialToCoefficientSeries (logPolynomialEuler N p)).coeff n).coeff j =
    (((n : K) • (logPolynomialToCoefficientSeries p).coeff n +
      N • ((logPolynomialToCoefficientSeries p).coeff n).derivative).coeff j)
  simp only [logPolynomialToCoefficientSeries_double_coeff,
    logPolynomialEuler_double_coeff, Polynomial.coeff_add,
    Polynomial.coeff_smul, Polynomial.coeff_derivative, smul_eq_mul]

/-- The operator after formally removing z^rho; no such exponent is adjoined. -/
def twistedLogPolynomialEuler (rho : K) (p : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  logPolynomialEuler (1 : K) p + rho • p

/-- Its polynomial-valued Laurent-series counterpart. -/
def twistedPolynomialCoefficientEuler (rho : K)
    (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  polynomialCoefficientEuler (1 : K) s + rho • s

theorem twistedPolynomialCoefficientEuler_coeff
    (rho : K) (s : LaurentSeries (Polynomial K)) (n : ℤ) :
    (twistedPolynomialCoefficientEuler rho s).coeff n =
      shiftedPolynomialDerivative (rho + (n : K)) (s.coeff n) := by
  change ((n : K) • s.coeff n + (1 : K) • (s.coeff n).derivative) +
    rho • s.coeff n = (s.coeff n).derivative + (rho + (n : K)) • s.coeff n
  rw [one_smul, add_smul]
  abel

theorem logPolynomialToCoefficientSeries_twistedEuler
    (rho : K) (p : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (twistedLogPolynomialEuler rho p) =
      twistedPolynomialCoefficientEuler rho (logPolynomialToCoefficientSeries p) := by
  rw [twistedLogPolynomialEuler, map_add, logPolynomialToCoefficientSeries_euler,
    logPolynomialToCoefficientSeries_smul]
  rfl

theorem logPolynomialToCoefficientSeries_twistedEuler_iterate
    (rho : K) (p : Polynomial (LaurentSeries K)) (i : ℕ) :
    logPolynomialToCoefficientSeries ((twistedLogPolynomialEuler rho)^[i] p) =
      (twistedPolynomialCoefficientEuler rho)^[i]
        (logPolynomialToCoefficientSeries p) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', logPolynomialToCoefficientSeries_twistedEuler,
      ih, Function.iterate_succ_apply']

theorem twistedPolynomialCoefficientEuler_iterate_coeff
    (rho : K) (s : LaurentSeries (Polynomial K)) (n : ℤ) (i : ℕ) :
    ((twistedPolynomialCoefficientEuler rho)^[i] s).coeff n =
      (shiftedPolynomialDerivative (rho + (n : K)))^[i] (s.coeff n) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', twistedPolynomialCoefficientEuler_coeff,
      ih, Function.iterate_succ_apply']

/-- Every iterate still comes from an actual power series, with the exact shift
rho+n at coefficient n. This proves negative support vanishing for all iterates. -/
theorem logPolynomialToCoefficientSeries_twistedEuler_iterate_powerSeries
    (rho : K) (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K))) (i : ℕ) :
    logPolynomialToCoefficientSeries ((twistedLogPolynomialEuler rho)^[i] p) =
      ((PowerSeries.mk (fun n =>
        (shiftedPolynomialDerivative (rho + (n : K)))^[i] (u n)) :
          PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) := by
  apply HahnSeries.ext
  funext n
  rw [logPolynomialToCoefficientSeries_twistedEuler_iterate,
    twistedPolynomialCoefficientEuler_iterate_coeff, hp]
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, LaurentSeries.coeff_coe_powerSeries,
      PowerSeries.coeff_mk, Int.cast_natCast]
  | negSucc n =>
    simp only [PowerSeries.coeff_coe, Int.negSucc_lt_zero, if_true, iterate_map_zero]

/-- Coefficient mapping commutes with the actual power-to-Laurent inclusion. -/
theorem logLaurentCoefficientMap_powerSeries (b : PowerSeries K) :
    logLaurentCoefficientMap (b : LaurentSeries K) =
      ((PowerSeries.map (Polynomial.C : K →+* Polynomial K) b :
        PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) := by
  apply HahnSeries.ext
  funext n
  rw [logLaurentCoefficientMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero Polynomial.C
  · exact (PowerSeries.coeff_map Polynomial.C n.natAbs b).symm

end StrictEUnit

#print axioms StrictEUnit.logLaurentCoefficientMap
#print axioms StrictEUnit.logPolynomialToCoefficientSeries
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_double_coeff
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_injective
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_smul
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_finiteLogLaurentTranspose
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_transpose_powerSeries_mk
#print axioms StrictEUnit.logPolynomial_negative_coeff_of_powerSeries
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_euler
#print axioms StrictEUnit.twistedLogPolynomialEuler
#print axioms StrictEUnit.twistedPolynomialCoefficientEuler
#print axioms StrictEUnit.twistedPolynomialCoefficientEuler_coeff
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_twistedEuler
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_twistedEuler_iterate
#print axioms StrictEUnit.twistedPolynomialCoefficientEuler_iterate_coeff
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_twistedEuler_iterate_powerSeries
#print axioms StrictEUnit.logLaurentCoefficientMap_powerSeries
