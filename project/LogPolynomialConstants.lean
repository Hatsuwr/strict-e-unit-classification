import LaurentEulerDerivation
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Constants in the polynomial logarithm extension

The operator is the actual coefficientwise Laurent Euler operator plus
N times the formal derivative in the new polynomial variable. Its coefficient
formula is proved. This file does not silently identify this polynomial ring
with an analytic logarithm extension or prove the rational-function-field
constant theorem. The operator is bundled as a derivation over ℤ; its
k-algebra scalar law is also proved separately.
-/
noncomputable section
open Polynomial HahnSeries
namespace StrictEUnit
variable {k : Type*} [Field k]

/-- Apply the actual Laurent Euler operator to every polynomial coefficient. -/
def coefficientEuler (p : Polynomial (LaurentSeries k)) : Polynomial (LaurentSeries k) :=
  Polynomial.ofFinsupp (p.toFinsupp.mapRange laurentEuler (by
    ext n
    simp only [laurentEuler_coeff, HahnSeries.coeff_zero, mul_zero]))

@[simp] theorem coefficientEuler_coeff (p : Polynomial (LaurentSeries k)) (n : ℕ) :
    (coefficientEuler p).coeff n = laurentEuler (p.coeff n) := rfl

/-- The formal logarithmic variable has derivative N. The constant series
`single 0 N` is the actual scalar multiplying the formal polynomial derivative. -/
def logPolynomialEuler (N : k) (p : Polynomial (LaurentSeries k)) :
    Polynomial (LaurentSeries k) :=
  coefficientEuler p + Polynomial.C (single (0 : ℤ) N) * p.derivative

@[simp] theorem logPolynomialEuler_coeff (N : k)
    (p : Polynomial (LaurentSeries k)) (n : ℕ) :
    (logPolynomialEuler N p).coeff n =
      laurentEuler (p.coeff n) + single (0 : ℤ) N *
        (p.coeff (n + 1) * (n + 1 : LaurentSeries k)) := by
  simp only [logPolynomialEuler, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    coefficientEuler_coeff, Polynomial.coeff_derivative]

/-- Extracting the Laurent constant term removes the Euler part exactly. -/
theorem logPolynomialEuler_coeff_constant (N : k)
    (p : Polynomial (LaurentSeries k)) (n : ℕ) :
    ((logPolynomialEuler N p).coeff n).coeff 0 =
      N * ((p.coeff (n + 1)).coeff 0 * (n + 1 : k)) := by
  rw [logPolynomialEuler_coeff, HahnSeries.coeff_add, laurentEuler_coeff_zero, zero_add]
  have hnat : (n + 1 : LaurentSeries k) = single (0 : ℤ) (n + 1 : k) := by
    simpa only [Nat.cast_add, Nat.cast_one, HahnSeries.C_apply] using
      (map_natCast (HahnSeries.C : k →+* LaurentSeries k) (n + 1)).symm
  rw [hnat]
  change (single (0 : ℤ) N * (p.coeff (n+1) * single (0 : ℤ) (n+1:k))).coeff (0+0) = _
  rw [HahnSeries.coeff_single_mul_add]
  change N * (p.coeff (n+1) * single (0 : ℤ) (n+1:k)).coeff (0+0) = _
  rw [HahnSeries.coeff_mul_single_add]

@[simp] theorem coefficientEuler_C (f : LaurentSeries k) :
    coefficientEuler (Polynomial.C f) = Polynomial.C (laurentEuler f) := by
  apply Polynomial.ext
  intro n
  simp only [coefficientEuler_coeff, Polynomial.coeff_C]
  by_cases hn : n = 0
  · simp only [hn, if_true]
  · simp only [hn, if_false]
    exact (laurentEulerDerivation (k := k)).map_zero

@[simp] theorem logPolynomialEuler_C (N : k) (f : LaurentSeries k) :
    logPolynomialEuler N (Polynomial.C f) = Polynomial.C (laurentEuler f) := by
  simp only [logPolynomialEuler, Polynomial.derivative_C, mul_zero, add_zero,
    coefficientEuler_C]

/-- Additivity is proved for the coefficientwise map itself. -/
theorem coefficientEuler_add (p q : Polynomial (LaurentSeries k)) :
    coefficientEuler (p + q) = coefficientEuler p + coefficientEuler q := by
  apply Polynomial.ext
  intro n
  simp only [coefficientEuler_coeff, Polynomial.coeff_add]
  exact (laurentEulerLinear (k := k)).map_add _ _

/-- Its product rule uses the actual Laurent Euler Leibniz identity in the
finite polynomial coefficient convolution. -/
theorem coefficientEuler_mul (p q : Polynomial (LaurentSeries k)) :
    coefficientEuler (p * q) = coefficientEuler p * q + p * coefficientEuler q := by
  apply Polynomial.ext
  intro n
  simp only [coefficientEuler_coeff, Polynomial.coeff_mul, Polynomial.coeff_add]
  rw [← laurentEulerLinear_apply, map_sum]
  simp only [laurentEulerLinear_apply, laurentEuler_mul, Finset.sum_add_distrib]

/-- Leibniz for the actual logarithmic polynomial operator. -/
theorem logPolynomialEuler_mul (N : k) (p q : Polynomial (LaurentSeries k)) :
    logPolynomialEuler N (p * q) =
      logPolynomialEuler N p * q + p * logPolynomialEuler N q := by
  simp only [logPolynomialEuler, coefficientEuler_mul, Polynomial.derivative_mul]
  ring

/-- Additivity of the actual logarithmic polynomial operator. -/
theorem logPolynomialEuler_add (N : k) (p q : Polynomial (LaurentSeries k)) :
    logPolynomialEuler N (p + q) = logPolynomialEuler N p + logPolynomialEuler N q := by
  simp only [logPolynomialEuler, coefficientEuler_add, Polynomial.derivative_add]
  ring

/-- The operator annihilates the actual base-field algebra map. -/
theorem logPolynomialEuler_algebraMap (N c : k) :
    logPolynomialEuler N (algebraMap k (Polynomial (LaurentSeries k)) c) = 0 := by
  rw [Polynomial.algebraMap_apply, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    logPolynomialEuler_C]
  have he := (laurentEulerDerivation (k := k)).map_algebraMap c
  have hz : laurentEuler (single (0 : ℤ) c) = 0 := by
    simpa only [laurentEulerDerivation_apply, LaurentSeries.algebraMap_apply,
      HahnSeries.C_apply] using he
  rw [hz, Polynomial.C_0]

/-- Scalar linearity follows from Leibniz and the proved scalar constants,
using the actual algebra structure rather than an assumed scalar-tower identification. -/
theorem logPolynomialEuler_smul (N c : k) (p : Polynomial (LaurentSeries k)) :
    logPolynomialEuler N (c • p) = c • logPolynomialEuler N p := by
  rw [Algebra.smul_def, Algebra.smul_def, logPolynomialEuler_mul,
    logPolynomialEuler_algebraMap, zero_mul, zero_add]

/-- The actual polynomial-log operator, bundled as a ring derivation
over ℤ. The separate theorem above also proves its k-scalar law for the
actual algebra action. All additivity and Leibniz obligations are proved. -/
def logPolynomialDerivation (N : k) :
    Derivation ℤ (Polynomial (LaurentSeries k)) (Polynomial (LaurentSeries k)) where
  toFun := logPolynomialEuler N
  map_add' := logPolynomialEuler_add N
  map_smul' := by
    intro c p
    let f : Polynomial (LaurentSeries k) →+ Polynomial (LaurentSeries k) :=
      { toFun := logPolynomialEuler N
        map_add' := logPolynomialEuler_add N
        map_zero' := by
          simpa only [map_zero] using logPolynomialEuler_algebraMap N (0 : k) }
    have hh := f.map_zsmul p c
    rw [Algebra.smul_def]
    have hmap : algebraMap ℤ (Polynomial (LaurentSeries k)) c =
        (c : Polynomial (LaurentSeries k)) := map_intCast _ c
    rw [hmap]
    simpa only [RingHom.id_apply, zsmul_eq_mul] using hh
  map_one_eq_zero' := by
    simpa only [map_one] using logPolynomialEuler_algebraMap N (1 : k)
  leibniz' := by
    intro p q
    change logPolynomialEuler N (p*q) = p * logPolynomialEuler N q + q * logPolynomialEuler N p
    rw [logPolynomialEuler_mul]
    ring

@[simp] theorem logPolynomialDerivation_apply (N : k) (p : Polynomial (LaurentSeries k)) :
    logPolynomialDerivation N p = logPolynomialEuler N p := rfl

/-- A constant of the logarithmic operator cannot have positive polynomial
degree. The leading Laurent coefficient is constant; the next polynomial
coefficient then yields N * degree * that nonzero constant = 0. -/
theorem logPolynomialEuler_natDegree_eq_zero [CharZero k]
    (N : k) (hN : N ≠ 0) (p : Polynomial (LaurentSeries k))
    (hp : logPolynomialEuler N p = 0) : p.natDegree = 0 := by
  by_contra hd
  have htop : laurentEuler (p.coeff p.natDegree) = 0 := by
    have h := congrArg (fun q : Polynomial (LaurentSeries k) => q.coeff p.natDegree) hp
    simpa only [logPolynomialEuler_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self p.natDegree),
      zero_mul, mul_zero, add_zero, Polynomial.coeff_zero] using h
  have htopform := (laurentEuler_eq_zero_iff (p.coeff p.natDegree)).mp htop
  have hdsub : p.natDegree - 1 + 1 = p.natDegree :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)
  have hdcast : ((p.natDegree - 1 : ℕ) : k) + 1 = (p.natDegree : k) := by
    exact_mod_cast hdsub
  have hnext := congrArg (fun q : Polynomial (LaurentSeries k) =>
    (q.coeff (p.natDegree - 1)).coeff 0) hp
  have hz : N * ((p.coeff p.natDegree).coeff 0 * (p.natDegree : k)) = 0 := by
    simpa only [logPolynomialEuler_coeff_constant, hdsub, hdcast,
      Polynomial.coeff_zero, HahnSeries.coeff_zero] using hnext
  have hdn : (p.natDegree : k) ≠ 0 := by exact_mod_cast hd
  have hc : (p.coeff p.natDegree).coeff 0 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hN)).resolve_right hdn
  have hlead : p.leadingCoeff = 0 := by
    rw [← Polynomial.coeff_natDegree, htopform, hc]
    simp
  have hpzero : p = 0 := Polynomial.leadingCoeff_eq_zero.mp hlead
  exact hd (by simp only [hpzero, Polynomial.natDegree_zero])

/-- The kernel consists exactly of constant polynomials whose Laurent value
is the actual constant series with coefficient in k. -/
theorem logPolynomialEuler_eq_zero_iff [CharZero k]
    (N : k) (hN : N ≠ 0) (p : Polynomial (LaurentSeries k)) :
    logPolynomialEuler N p = 0 ↔
      p = Polynomial.C (single (0 : ℤ) ((p.coeff 0).coeff 0)) := by
  constructor
  · intro hp
    have hc := Polynomial.eq_C_of_natDegree_eq_zero
      (logPolynomialEuler_natDegree_eq_zero N hN p hp)
    have he : laurentEuler (p.coeff 0) = 0 := by
      have hh := hp
      rw [hc, logPolynomialEuler_C, Polynomial.C_eq_zero] at hh
      exact hh
    exact hc.trans (congrArg Polynomial.C ((laurentEuler_eq_zero_iff _).mp he))
  · intro hp
    rw [hp, logPolynomialEuler_C]
    have he : laurentEuler (single (0 : ℤ) ((p.coeff 0).coeff 0)) = 0 := by
      apply (laurentEuler_eq_zero_iff _).mpr
      simp
    rw [he, Polynomial.C_0]

/-- Existential form, with no hidden transcendental constant field. -/
theorem logPolynomialEuler_eq_zero_iff_exists_scalar [CharZero k]
    (N : k) (hN : N ≠ 0) (p : Polynomial (LaurentSeries k)) :
    logPolynomialEuler N p = 0 ↔ ∃ c : k, p = Polynomial.C (single (0 : ℤ) c) := by
  constructor
  · intro hp
    exact ⟨(p.coeff 0).coeff 0, (logPolynomialEuler_eq_zero_iff N hN p).mp hp⟩
  · rintro ⟨c, rfl⟩
    apply (logPolynomialEuler_eq_zero_iff N hN _).mpr
    simp

end StrictEUnit

#print axioms StrictEUnit.coefficientEuler
#print axioms StrictEUnit.coefficientEuler_coeff
#print axioms StrictEUnit.logPolynomialEuler
#print axioms StrictEUnit.logPolynomialEuler_coeff
#print axioms StrictEUnit.logPolynomialEuler_coeff_constant
#print axioms StrictEUnit.coefficientEuler_C
#print axioms StrictEUnit.logPolynomialEuler_C
#print axioms StrictEUnit.logPolynomialEuler_natDegree_eq_zero
#print axioms StrictEUnit.logPolynomialEuler_eq_zero_iff
#print axioms StrictEUnit.logPolynomialEuler_eq_zero_iff_exists_scalar

#print axioms StrictEUnit.coefficientEuler_add
#print axioms StrictEUnit.coefficientEuler_mul
#print axioms StrictEUnit.logPolynomialEuler_add
#print axioms StrictEUnit.logPolynomialEuler_mul

#print axioms StrictEUnit.logPolynomialEuler_algebraMap
#print axioms StrictEUnit.logPolynomialEuler_smul
#print axioms StrictEUnit.logPolynomialDerivation
#print axioms StrictEUnit.logPolynomialDerivation_apply
