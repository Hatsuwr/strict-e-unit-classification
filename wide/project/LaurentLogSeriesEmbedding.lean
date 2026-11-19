import LaurentLogBase
import LogPolynomialConstants
import Mathlib.FieldTheory.RatFunc.Basic
import ManuscriptBaseSimplicity
import Mathlib.Tactic.FieldSimp
import RationalDerivationExtension

/-!
# The actual formal Laurent-series embedding of the manuscript base

Finite Laurent polynomials embed coefficientwise in actual Laurent series.
The extra polynomial variable is retained as a formal variable. Injectivity
is proved from coefficients, and the induced fraction-field embedding is
constructed. No analytic logarithm, convergence, or analytic continuation is
assumed by this formal-series construction.
-/
noncomputable section
open Polynomial HahnSeries
namespace StrictEUnit
variable {k : Type*} [Field k]

/-- Laurent monomials as actual single-term Laurent series. -/
def seriesMonomialHom : Multiplicative ℤ →* LaurentSeries k where
  toFun n := single n.toAdd (1 : k)
  map_one' := rfl
  map_mul' := by
    intro n m
    change single (n.toAdd + m.toAdd) (1 : k) = single n.toAdd 1 * single m.toAdd 1
    rw [HahnSeries.single_mul_single, one_mul]

/-- The actual finite-Laurent-series inclusion, built by the monoid-algebra
universal property rather than an assumed embedding. -/
def laurentPolynomialToSeries : LaurentPolynomial k →ₐ[k] LaurentSeries k :=
  AddMonoidAlgebra.lift k ℤ (LaurentSeries k) seriesMonomialHom

@[simp] theorem laurentPolynomialToSeries_single (n : ℤ) (a : k) :
    laurentPolynomialToSeries (AddMonoidAlgebra.single n a) = single n a := by
  rw [laurentPolynomialToSeries, AddMonoidAlgebra.lift_single]
  rw [Algebra.smul_def, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
  change single (0 : ℤ) a * single n (1 : k) = single n a
  rw [HahnSeries.single_mul_single, zero_add, mul_one]

/-- The embedding preserves each integer-indexed coefficient literally. -/
@[simp] theorem laurentPolynomialToSeries_coeff (f : LaurentPolynomial k) (n : ℤ) :
    (laurentPolynomialToSeries f).coeff n = f n := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, HahnSeries.coeff_add, hf, hg, Finsupp.add_apply]
  | single m a =>
    simp only [laurentPolynomialToSeries_single, HahnSeries.coeff_single,
      Finsupp.single_apply, eq_comm]
    split_ifs <;> rfl

theorem laurentPolynomialToSeries_injective :
    Function.Injective (laurentPolynomialToSeries (k := k)) := by
  intro f g h
  apply Finsupp.ext
  intro n
  simpa only [laurentPolynomialToSeries_coeff] using
    congrArg (fun x : LaurentSeries k => x.coeff n) h

/-- Extend the coefficient inclusion, preserving the formal logarithmic variable. -/
def laurentLogToSeriesPolynomial : LaurentLogBase k →+* Polynomial (LaurentSeries k) :=
  Polynomial.mapRingHom laurentPolynomialToSeries.toRingHom

@[simp] theorem laurentLogToSeriesPolynomial_coeff (p : LaurentLogBase k) (j : ℕ) (n : ℤ) :
    ((laurentLogToSeriesPolynomial p).coeff j).coeff n = (p.coeff j) n := by
  change ((p.map laurentPolynomialToSeries.toRingHom).coeff j).coeff n = _
  rw [Polynomial.coeff_map]
  exact laurentPolynomialToSeries_coeff _ _

theorem laurentLogToSeriesPolynomial_injective :
    Function.Injective (laurentLogToSeriesPolynomial (k := k)) :=
  Polynomial.map_injective laurentPolynomialToSeries.toRingHom
    laurentPolynomialToSeries_injective

/-- The same base algebra inside the actual rational-function field over
Laurent series. -/
def laurentLogToRatFunc : LaurentLogBase k →+* RatFunc (LaurentSeries k) :=
  (algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))).comp
    laurentLogToSeriesPolynomial

theorem laurentLogToRatFunc_injective : Function.Injective (laurentLogToRatFunc (k := k)) :=
  (IsFractionRing.injective (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))).comp
    laurentLogToSeriesPolynomial_injective

/-- The induced field embedding is constructed by localization. -/
def laurentLogFractionToRatFunc :
    FractionRing (LaurentLogBase k) →+* RatFunc (LaurentSeries k) :=
  IsFractionRing.lift laurentLogToRatFunc_injective

theorem laurentLogFractionToRatFunc_injective :
    Function.Injective (laurentLogFractionToRatFunc (k := k)) :=
  (laurentLogFractionToRatFunc (k := k)).injective

@[simp] theorem laurentLogFractionToRatFunc_algebraMap (p : LaurentLogBase k) :
    laurentLogFractionToRatFunc (algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k)) p) =
      laurentLogToRatFunc p := IsFractionRing.lift_algebraMap _ p

/-- The full double-coefficient formula of the logarithmic series operator. -/
theorem logPolynomialEuler_double_coeff (N : k)
    (p : Polynomial (LaurentSeries k)) (j : ℕ) (n : ℤ) :
    ((logPolynomialEuler N p).coeff j).coeff n =
      (n : k) * (p.coeff j).coeff n +
        N * ((p.coeff (j + 1)).coeff n * (j + 1 : k)) := by
  rw [logPolynomialEuler_coeff, HahnSeries.coeff_add, laurentEuler_coeff]
  have hj : (j + 1 : LaurentSeries k) = single (0 : ℤ) (j + 1 : k) := by
    simpa only [Nat.cast_add, Nat.cast_one, HahnSeries.C_apply] using
      (map_natCast (HahnSeries.C : k →+* LaurentSeries k) (j + 1)).symm
  rw [hj]
  congr 1
  calc
    (single (0 : ℤ) N * (p.coeff (j+1) * single (0 : ℤ) (j+1:k))).coeff n =
        N * (p.coeff (j+1) * single (0 : ℤ) (j+1:k)).coeff n := by
      simpa only [add_zero] using (HahnSeries.coeff_single_mul_add
        (a := n) (b := (0 : ℤ)) (r := N)
        (x := p.coeff (j+1) * single (0 : ℤ) (j+1:k)))
    _ = N * ((p.coeff (j+1)).coeff n * (j+1:k)) := by
      congr 1
      simpa only [add_zero] using (HahnSeries.coeff_mul_single_add
        (a := n) (b := (0 : ℤ)) (r := (j+1:k)) (x := p.coeff (j+1)))

/-- Compatibility with the manuscript's precise scale: D(t)=t/N and
D(ell)=1 correspond to N⁻¹ times the series Euler-plus-N-log derivative.
The multiplier is displayed as an actual constant polynomial. -/
theorem laurentLogToSeriesPolynomial_derivation [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (p : LaurentLogBase k) :
    laurentLogToSeriesPolynomial (manuscriptBaseDerivation N p) =
      Polynomial.C (single (0 : ℤ) ((N : k)⁻¹)) *
        logPolynomialEuler (N : k) (laurentLogToSeriesPolynomial p) := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  rw [laurentLogToSeriesPolynomial_coeff, manuscriptBaseDerivation_coeff,
    Polynomial.coeff_C_mul]
  rw [← add_zero n, HahnSeries.coeff_single_mul_add]
  simp only [add_zero]
  rw [logPolynomialEuler_double_coeff,
    laurentLogToSeriesPolynomial_coeff, laurentLogToSeriesPolynomial_coeff]
  have hNk : (N : k) ≠ 0 := by exact_mod_cast hN
  field_simp [hNk]
  ring

/-- Explicit scalar compatibility for the fraction-field embedding. -/
@[simp] theorem laurentLogFractionToRatFunc_scalar (c : k) :
    laurentLogFractionToRatFunc
      (algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k))
        (Polynomial.C (AddMonoidAlgebra.single (0 : ℤ) c))) =
      algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
        (Polynomial.C (HahnSeries.single (0 : ℤ) c)) := by
  rw [laurentLogFractionToRatFunc_algebraMap]
  change algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
    ((Polynomial.C (AddMonoidAlgebra.single (0 : ℤ) c)).map
      laurentPolynomialToSeries.toRingHom) = _
  rw [Polynomial.map_C]
  congr 2
  exact laurentPolynomialToSeries_single _ _

/-- There are no extra constants among embedded base-fraction elements:
vanishing of the actual ambient rational derivation forces an actual scalar
in the original fraction field. This does not define a source-field
derivation or assume its existence. -/
theorem embedded_laurentLog_fraction_constants [CharZero k]
    (N : k) (hN : N ≠ 0) (f : FractionRing (LaurentLogBase k)) :
    logRationalDerivation N (laurentLogFractionToRatFunc f) = 0 ↔
      ∃ c : k, f = algebraMap (LaurentLogBase k) (FractionRing (LaurentLogBase k))
        (Polynomial.C (AddMonoidAlgebra.single (0 : ℤ) c)) := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := (logRationalDerivation_constants N hN _).mp hf
    refine ⟨c, laurentLogFractionToRatFunc_injective ?_⟩
    rw [laurentLogFractionToRatFunc_scalar]
    exact hc
  · rintro ⟨c, rfl⟩
    rw [laurentLogFractionToRatFunc_scalar]
    apply (logRationalDerivation_constants N hN _).mpr
    exact ⟨c, rfl⟩

end StrictEUnit

#print axioms StrictEUnit.seriesMonomialHom
#print axioms StrictEUnit.laurentPolynomialToSeries
#print axioms StrictEUnit.laurentPolynomialToSeries_single
#print axioms StrictEUnit.laurentPolynomialToSeries_coeff
#print axioms StrictEUnit.laurentPolynomialToSeries_injective
#print axioms StrictEUnit.laurentLogToSeriesPolynomial
#print axioms StrictEUnit.laurentLogToSeriesPolynomial_coeff
#print axioms StrictEUnit.laurentLogToSeriesPolynomial_injective
#print axioms StrictEUnit.laurentLogToRatFunc
#print axioms StrictEUnit.laurentLogToRatFunc_injective
#print axioms StrictEUnit.laurentLogFractionToRatFunc
#print axioms StrictEUnit.laurentLogFractionToRatFunc_injective
#print axioms StrictEUnit.laurentLogFractionToRatFunc_algebraMap

#print axioms StrictEUnit.logPolynomialEuler_double_coeff
#print axioms StrictEUnit.laurentLogToSeriesPolynomial_derivation

#print axioms StrictEUnit.laurentLogFractionToRatFunc_scalar
#print axioms StrictEUnit.embedded_laurentLog_fraction_constants
