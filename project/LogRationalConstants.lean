import LogPolynomialConstants
import Mathlib.FieldTheory.RatFunc.Basic

/-! Normalized-denominator reduction for rational constants. The quotient
operator below is defined on actual normalized numerators and denominators;
its derivation laws are not assumed or asserted by this definition. -/
noncomputable section
namespace StrictEUnit
open Polynomial
variable {K : Type*} [Field K]

/-- Coprimality and the cross-derivative equation force denominator divisibility. -/
theorem denominator_dvd_image (D : K[X] → K[X]) (p q : K[X])
    (hcop : IsCoprime p q) (hcross : D p * q = p * D q) : q ∣ D q := by
  apply hcop.symm.dvd_of_dvd_mul_left
  rw [← hcross]
  exact dvd_mul_left q (D p)

/-- A derivative of strictly lower degree cannot be divisible by its denominator. -/
theorem denominator_image_zero (D : K[X] → K[X]) (p q : K[X])
    (hcop : IsCoprime p q) (hcross : D p * q = p * D q)
    (hdeg : (D q).degree < q.degree) : D q = 0 := by
  by_contra hz
  exact (not_lt_of_ge (Polynomial.degree_le_of_dvd
    (denominator_dvd_image D p q hcop hcross) hz)) hdeg

/-- The quotient-rule expression on the canonical coprime, monic presentation. -/
def rationalQuotientOperator (D : K[X] → K[X]) (f : RatFunc K) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (D f.num) * algebraMap K[X] (RatFunc K) f.denom -
    algebraMap K[X] (RatFunc K) f.num * algebraMap K[X] (RatFunc K) (D f.denom)) /
      (algebraMap K[X] (RatFunc K) f.denom)^2

theorem rationalQuotientOperator_eq_zero_iff (D : K[X] → K[X]) (f : RatFunc K) :
    rationalQuotientOperator D f = 0 ↔ D f.num * f.denom = f.num * D f.denom := by
  unfold rationalQuotientOperator
  rw [_root_.div_eq_zero_iff]
  have hq : (algebraMap K[X] (RatFunc K) f.denom)^2 ≠ 0 :=
    pow_ne_zero _ (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f))
  simp only [hq, or_false, sub_eq_zero, ← map_mul]
  exact (IsFractionRing.injective K[X] (RatFunc K)).eq_iff

theorem rational_denominator_image_zero (D : K[X] → K[X]) (f : RatFunc K)
    (hf : rationalQuotientOperator D f = 0)
    (hdeg : (D f.denom).degree < f.denom.degree) : D f.denom = 0 :=
  denominator_image_zero D f.num f.denom (RatFunc.isCoprime_num_denom f)
    ((rationalQuotientOperator_eq_zero_iff D f).mp hf) hdeg

/-- Every genuine fraction-field derivation extending D agrees with the
canonical quotient-rule expression. This does not assert existence of the extension. -/
theorem derivation_eq_rationalQuotientOperator
    {S : Type*} [CommRing S] [Algebra S (RatFunc K)]
    (d : Derivation S (RatFunc K) (RatFunc K)) (D : K[X] → K[X])
    (hext : ∀ p, d (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (D p)) (f : RatFunc K) :
    d f = rationalQuotientOperator D f := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  have hd := Derivation.leibniz_div (R:=S) (M:=RatFunc K) d (algebraMap K[X] (RatFunc K) f.num)
    (algebraMap K[X] (RatFunc K) f.denom)
  rw [hd, hext, hext]
  simp only [rationalQuotientOperator, smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

/-- The complete normalized-denominator reduction, with the two polynomial
facts exposed explicitly for subsequent concrete specialization. -/
theorem rational_constant_reduction {C : Type*} (embed : C → K)
    (D : K[X] → K[X])
    (hdrop : ∀ q : K[X], q.Monic → (D q).degree < q.degree)
    (hkernel : ∀ p : K[X], D p = 0 → ∃ c : C, p = Polynomial.C (embed c))
    (f : RatFunc K) (hf : rationalQuotientOperator D f = 0) :
    ∃ c : C, f = algebraMap K[X] (RatFunc K) (Polynomial.C (embed c)) := by
  have hq := rational_denominator_image_zero D f hf
    (hdrop f.denom (RatFunc.monic_denom f))
  obtain ⟨c, hc⟩ := hkernel f.denom hq
  have hq1 : f.denom = 1 := by
    apply Polynomial.eq_one_of_monic_natDegree_zero (RatFunc.monic_denom f)
    rw [hc, Polynomial.natDegree_C]
  have hp : D f.num = 0 := by
    have hcross := (rationalQuotientOperator_eq_zero_iff D f).mp hf
    rw [hq, hq1, mul_one, mul_zero] at hcross
    exact hcross
  obtain ⟨c, hc⟩ := hkernel f.num hp
  refine ⟨c, ?_⟩
  rw [← RatFunc.num_div_denom f, hc, hq1, map_one, div_one]

section ActualLog
variable {k : Type*} [Field k]

/-- Monicity cancels the highest coefficient of the actual logarithmic operator. -/
theorem logPolynomialEuler_degree_lt_of_monic (N : k)
    (q : Polynomial (LaurentSeries k)) (hq : q.Monic) :
    (logPolynomialEuler N q).degree < q.degree := by
  rw [Polynomial.degree_eq_natDegree hq.ne_zero]
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro m hm
  rw [logPolynomialEuler_coeff]
  have hn : q.coeff (m+1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hn, zero_mul, mul_zero, add_zero]
  by_cases he : m = q.natDegree
  · subst m
    rw [hq.coeff_natDegree]
    exact laurentEulerDerivation.map_one_eq_zero
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact laurentEulerLinear.map_zero

/-- The concrete quotient-rule operator on Laurent-series rational functions. -/
def logRationalEuler (N : k) : RatFunc (LaurentSeries k) → RatFunc (LaurentSeries k) :=
  rationalQuotientOperator (logPolynomialEuler N)

/-- The concrete rational quotient-rule kernel has no extra constants.
Identifying this operator with a bundled fraction derivation is separate. -/
theorem logRationalEuler_eq_zero_implies_scalar [CharZero k]
    (N : k) (hN : N ≠ 0) (f : RatFunc (LaurentSeries k))
    (hf : logRationalEuler N f = 0) :
    ∃ c : k, f = algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
      (Polynomial.C (HahnSeries.single (0:ℤ) c)) := by
  exact rational_constant_reduction (fun c : k => HahnSeries.single (0:ℤ) c)
    (logPolynomialEuler N) (logPolynomialEuler_degree_lt_of_monic N)
    (fun p hp => (logPolynomialEuler_eq_zero_iff_exists_scalar N hN p).mp hp) f hf

theorem logRationalEuler_eq_zero_iff_exists_scalar [CharZero k]
    (N : k) (hN : N ≠ 0) (f : RatFunc (LaurentSeries k)) :
    logRationalEuler N f = 0 ↔
      ∃ c : k, f = algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
        (Polynomial.C (HahnSeries.single (0:ℤ) c)) := by
  constructor
  · exact logRationalEuler_eq_zero_implies_scalar N hN f
  · rintro ⟨c, rfl⟩
    apply (rationalQuotientOperator_eq_zero_iff _ _).mpr
    rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
    have hp : logPolynomialEuler N (Polynomial.C (HahnSeries.single (0:ℤ) c)) = 0 :=
      (logPolynomialEuler_eq_zero_iff_exists_scalar N hN _).mpr ⟨c, rfl⟩
    have h1 : logPolynomialEuler N (1 : Polynomial (LaurentSeries k)) = 0 := by
      apply (logPolynomialEuler_eq_zero_iff_exists_scalar N hN _).mpr
      refine ⟨1, ?_⟩
      rfl
    rw [hp, h1, zero_mul, mul_zero]

/-- For any actual fraction derivation extending the concrete polynomial
operator, the rational constants are exactly k. Only extension existence
is left as an external obligation; the constants conclusion is proved. -/
theorem extending_log_derivation_constants [CharZero k]
    (N : k) (hN : N ≠ 0)
    (d : Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)))
    (hext : ∀ p : Polynomial (LaurentSeries k),
      d (algebraMap _ (RatFunc (LaurentSeries k)) p) =
        algebraMap _ (RatFunc (LaurentSeries k)) (logPolynomialEuler N p))
    (f : RatFunc (LaurentSeries k)) :
    d f = 0 ↔ ∃ c : k,
      f = algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
        (Polynomial.C (HahnSeries.single (0:ℤ) c)) := by
  rw [derivation_eq_rationalQuotientOperator d (logPolynomialEuler N) hext f]
  exact logRationalEuler_eq_zero_iff_exists_scalar N hN f

end ActualLog
end StrictEUnit

#print axioms StrictEUnit.denominator_dvd_image

#print axioms StrictEUnit.denominator_image_zero

#print axioms StrictEUnit.rationalQuotientOperator

#print axioms StrictEUnit.rationalQuotientOperator_eq_zero_iff

#print axioms StrictEUnit.rational_denominator_image_zero

#print axioms StrictEUnit.derivation_eq_rationalQuotientOperator

#print axioms StrictEUnit.rational_constant_reduction

#print axioms StrictEUnit.logPolynomialEuler_degree_lt_of_monic

#print axioms StrictEUnit.logRationalEuler

#print axioms StrictEUnit.logRationalEuler_eq_zero_implies_scalar

#print axioms StrictEUnit.logRationalEuler_eq_zero_iff_exists_scalar

#print axioms StrictEUnit.extending_log_derivation_constants
