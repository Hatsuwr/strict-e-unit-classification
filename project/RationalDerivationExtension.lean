import LogRationalConstants

/-! Construction of the fraction-field derivation from the actual
quotient rule. Presentation independence is proved by differentiating the
cross-multiplication equation. -/
noncomputable section
set_option maxHeartbeats 200000
namespace StrictEUnit
open Polynomial
variable {F : Type*} [Field F]

theorem quotient_rule_cross_invariant (n d p q nd dd pd qd : F)
    (hd0 : d ≠ 0) (hq0 : q ≠ 0)
    (h : n*q = p*d) (hD : nd*q + n*qd = pd*d + p*dd) :
    (nd*d-n*dd)/d^2 = (pd*q-p*qd)/q^2 := by
  apply (_root_.div_eq_div_iff (pow_ne_zero _ hd0) (pow_ne_zero _ hq0)).mpr
  linear_combination d*q*hD - (dd*q+qd*d)*h

variable {K : Type*} [Field K] [Algebra ℤ K]

/-- The normalized expression agrees with the quotient rule for every
nonzero polynomial denominator, not only the chosen monic denominator. -/
theorem rationalQuotientOperator_apply_div
    (D : Derivation ℤ K[X] K[X]) (p q : K[X]) (hq : q ≠ 0) :
    rationalQuotientOperator D
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
    (algebraMap K[X] (RatFunc K) (D p) * algebraMap K[X] (RatFunc K) q -
      algebraMap K[X] (RatFunc K) p * algebraMap K[X] (RatFunc K) (D q)) /
        (algebraMap K[X] (RatFunc K) q)^2 := by
  let f : RatFunc K := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q
  have hcross : f.num*q = p*f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl
  have hD : D f.num*q + f.num*D q = D p*f.denom + p*D f.denom := by
    have h := congrArg D hcross
    simp only [D.leibniz, smul_eq_mul] at h
    convert h using 1 <;> ring
  apply quotient_rule_cross_invariant
    (algebraMap K[X] (RatFunc K) f.num) (algebraMap K[X] (RatFunc K) f.denom)
    (algebraMap K[X] (RatFunc K) p) (algebraMap K[X] (RatFunc K) q)
    (algebraMap K[X] (RatFunc K) (D f.num)) (algebraMap K[X] (RatFunc K) (D f.denom))
    (algebraMap K[X] (RatFunc K) (D p)) (algebraMap K[X] (RatFunc K) (D q))
    (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)) (RatFunc.algebraMap_ne_zero hq)
  · simpa only [map_mul] using congrArg (algebraMap K[X] (RatFunc K)) hcross
  · simpa only [map_add, map_mul] using congrArg (algebraMap K[X] (RatFunc K)) hD

theorem rationalQuotientOperator_add (D : Derivation ℤ K[X] K[X]) (f g : RatFunc K) :
    rationalQuotientOperator D (f+g) =
      rationalQuotientOperator D f + rationalQuotientOperator D g := by
  induction f using RatFunc.induction_on
  rename_i p q hq
  induction g using RatFunc.induction_on
  rename_i r s hs
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hs' := RatFunc.algebraMap_ne_zero hs
  have hadd : algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q +
      algebraMap K[X] (RatFunc K) r / algebraMap K[X] (RatFunc K) s =
      algebraMap K[X] (RatFunc K) (p*s+q*r) / algebraMap K[X] (RatFunc K) (q*s) := by
    simp only [map_add, map_mul]
    field_simp
    ring
  rw [hadd, rationalQuotientOperator_apply_div D _ _ (mul_ne_zero hq hs),
    rationalQuotientOperator_apply_div D p q hq, rationalQuotientOperator_apply_div D r s hs]
  simp only [map_add, map_mul, D.leibniz, smul_eq_mul]
  field_simp
  ring

theorem rationalQuotientOperator_mul (D : Derivation ℤ K[X] K[X]) (f g : RatFunc K) :
    rationalQuotientOperator D (f*g) =
      rationalQuotientOperator D f * g + f * rationalQuotientOperator D g := by
  induction f using RatFunc.induction_on
  rename_i p q hq
  induction g using RatFunc.induction_on
  rename_i r s hs
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hs' := RatFunc.algebraMap_ne_zero hs
  rw [div_mul_div_comm, ← map_mul, ← map_mul,
    rationalQuotientOperator_apply_div D _ _ (mul_ne_zero hq hs),
    rationalQuotientOperator_apply_div D p q hq, rationalQuotientOperator_apply_div D r s hs]
  simp only [D.leibniz, smul_eq_mul, map_add, map_mul]
  field_simp
  ring

def rationalQuotientAddHom (D : Derivation ℤ K[X] K[X]) : RatFunc K →+ RatFunc K where
  toFun := rationalQuotientOperator D
  map_add' := rationalQuotientOperator_add D
  map_zero' := by
    have h : rationalQuotientOperator D 0 + rationalQuotientOperator D 0 =
        rationalQuotientOperator D 0 + 0 := by
      simpa only [zero_add, add_zero] using (rationalQuotientOperator_add D 0 0).symm
    exact add_left_cancel h

/-- The actual fraction-field derivation, with no extension-existence hypothesis. -/
def rationalDerivationExtension (D : Derivation ℤ K[X] K[X]) :
    Derivation ℤ (RatFunc K) (RatFunc K) where
  toFun := rationalQuotientOperator D
  map_add' := rationalQuotientOperator_add D
  map_smul' := by
    intro c f
    have h := (rationalQuotientAddHom D).map_zsmul f c
    rw [Algebra.smul_def]
    have hmap : algebraMap ℤ (RatFunc K) c = (c : RatFunc K) := map_intCast _ c
    rw [hmap]
    simpa only [RingHom.id_apply, zsmul_eq_mul] using h
  map_one_eq_zero' := by
    simp [rationalQuotientOperator, D.map_one_eq_zero]
  leibniz' := by
    intro f g
    change rationalQuotientOperator D (f*g) =
      f * rationalQuotientOperator D g + g * rationalQuotientOperator D f
    rw [rationalQuotientOperator_mul]
    ring

@[simp] theorem rationalDerivationExtension_apply (D : Derivation ℤ K[X] K[X]) (f : RatFunc K) :
    rationalDerivationExtension D f = rationalQuotientOperator D f := rfl

@[simp] theorem rationalDerivationExtension_algebraMap
    (D : Derivation ℤ K[X] K[X]) (p : K[X]) :
    rationalDerivationExtension D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (D p) := by
  have h := rationalQuotientOperator_apply_div D p 1 one_ne_zero
  simpa only [map_one, div_one, D.map_one_eq_zero, map_zero, mul_one, mul_zero,
    sub_zero, one_pow] using h

section ActualLog
variable {k : Type*} [Field k]

/-- The actual derivation on k((t))(ell), with D(t)=t and D(ell)=N. -/
def logRationalDerivation (N : k) :
    Derivation ℤ (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)) :=
  rationalDerivationExtension (K:=LaurentSeries k) (logPolynomialDerivation N)

@[simp] theorem logRationalDerivation_apply (N : k) (f : RatFunc (LaurentSeries k)) :
    logRationalDerivation N f = logRationalEuler N f := rfl

/-- The actual fraction-field derivation has exactly the original constants.
There is no assumed derivation-extension or no-extra-constants premise. -/
theorem logRationalDerivation_constants [CharZero k]
    (N : k) (hN : N ≠ 0) (f : RatFunc (LaurentSeries k)) :
    logRationalDerivation N f = 0 ↔ ∃ c : k,
      f = algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
        (Polynomial.C (HahnSeries.single (0:ℤ) c)) :=
  logRationalEuler_eq_zero_iff_exists_scalar N hN f

/-- Laurent-series coefficients keep their actual Euler derivative. -/
theorem logRationalDerivation_C (N : k) (a : LaurentSeries k) :
    logRationalDerivation N
      (algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k)) (Polynomial.C a)) =
      algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
        (Polynomial.C (laurentEuler a)) := by
  change rationalDerivationExtension (K:=LaurentSeries k) (logPolynomialDerivation N) _ = _
  rw [rationalDerivationExtension_algebraMap, logPolynomialDerivation_apply,
    logPolynomialEuler_C]

/-- The adjoined logarithm has derivative exactly N. -/
theorem logRationalDerivation_X (N : k) :
    logRationalDerivation N
      (algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k)) Polynomial.X) =
      algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
        (Polynomial.C (HahnSeries.single (0:ℤ) N)) := by
  change rationalDerivationExtension (K:=LaurentSeries k) (logPolynomialDerivation N) _ = _
  rw [rationalDerivationExtension_algebraMap, logPolynomialDerivation_apply]
  congr 1
  have hE : coefficientEuler (Polynomial.X : Polynomial (LaurentSeries k)) = 0 := by
    apply Polynomial.ext
    intro n
    rw [coefficientEuler_coeff, Polynomial.coeff_zero]
    by_cases hn : n = 1
    · subst n
      simp only [Polynomial.coeff_X_one]
      exact (laurentEulerDerivation (k:=k)).map_one_eq_zero
    · rw [Polynomial.coeff_X, if_neg (Ne.symm hn)]
      exact (laurentEulerLinear (k:=k)).map_zero
  simp only [logPolynomialEuler, hE, Polynomial.derivative_X, mul_one, zero_add]

end ActualLog
end StrictEUnit

#print axioms StrictEUnit.quotient_rule_cross_invariant
#print axioms StrictEUnit.rationalQuotientOperator_apply_div
#print axioms StrictEUnit.rationalQuotientOperator_add
#print axioms StrictEUnit.rationalQuotientOperator_mul
#print axioms StrictEUnit.rationalQuotientAddHom
#print axioms StrictEUnit.rationalDerivationExtension
#print axioms StrictEUnit.rationalDerivationExtension_apply
#print axioms StrictEUnit.rationalDerivationExtension_algebraMap
#print axioms StrictEUnit.logRationalDerivation
#print axioms StrictEUnit.logRationalDerivation_apply
#print axioms StrictEUnit.logRationalDerivation_constants
#print axioms StrictEUnit.logRationalDerivation_C
#print axioms StrictEUnit.logRationalDerivation_X
