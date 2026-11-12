import Stage14RationalOrdinaryDerivation
import LaurentOrdinaryDerivation
import Stage14PolynomialScalarODEClosure

/-! Instantiation of polynomial differential-equation closure in the actual
Laurent-series field with its ordinary derivative and rational-function scalars. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]

/-- The underlying ordinary Laurent derivative, separated from module-instance
presentation so it can be rebundled with the canonical algebra module. -/
def stage14_laurentDerivativeFun : LaurentSeries k → LaurentSeries k :=
  laurentOrdinaryDerivation

theorem stage14_laurentDerivativeFun_add (f g : LaurentSeries k) :
    stage14_laurentDerivativeFun (f + g) =
      stage14_laurentDerivativeFun f + stage14_laurentDerivativeFun g :=
  (laurentOrdinaryDerivation (k := k)).map_add f g

theorem stage14_laurentDerivativeFun_scalar (c : k) (f : LaurentSeries k) :
    stage14_laurentDerivativeFun (algebraMap k (LaurentSeries k) c * f) =
      algebraMap k (LaurentSeries k) c * stage14_laurentDerivativeFun f := by
  ext n
  simp only [stage14_laurentDerivativeFun, LaurentSeries.algebraMap_apply,
    HahnSeries.C_mul_eq_smul, laurentOrdinaryDerivation_coeff,
    HahnSeries.coeff_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem stage14_laurentDerivativeFun_one :
    stage14_laurentDerivativeFun (1 : LaurentSeries k) = 0 :=
  (laurentOrdinaryDerivation (k := k)).map_one_eq_zero

theorem stage14_laurentDerivativeFun_mul (f g : LaurentSeries k) :
    stage14_laurentDerivativeFun (f * g) =
      f * stage14_laurentDerivativeFun g + g * stage14_laurentDerivativeFun f :=
  (laurentOrdinaryDerivation (k := k)).leibniz f g

/-- Rebundle the very same actual Laurent derivative with the canonical algebra
module. Equality of scalar actions is proved, not added as an axiom or instance. -/
def stage14_laurentAlgebraDerivation :
    @Derivation k (LaurentSeries k) (LaurentSeries k) _ _ _ _ _
      (Algebra.toModule : Module k (LaurentSeries k)) := by
  letI : SMul k (LaurentSeries k) := Algebra.toSMul
  letI : Module k (LaurentSeries k) := Algebra.toModule
  exact {
    toFun := stage14_laurentDerivativeFun
    map_add' := stage14_laurentDerivativeFun_add
    map_smul' := fun c f => by
      change stage14_laurentDerivativeFun (algebraMap k (LaurentSeries k) c * f) =
        algebraMap k (LaurentSeries k) c * stage14_laurentDerivativeFun f
      exact stage14_laurentDerivativeFun_scalar c f
    map_one_eq_zero' := stage14_laurentDerivativeFun_one
    leibniz' := stage14_laurentDerivativeFun_mul }

/-- The rebundling does not change the derivative function. -/
@[simp] theorem stage14_laurentAlgebraDerivation_apply (f : LaurentSeries k) :
    stage14_laurentAlgebraDerivation f = laurentOrdinaryDerivation f := rfl

/-- The standard scalar algebra maps form a tower, supplied explicitly rather
than registered as a global instance. -/
def stage14_rationalLaurentScalarTower :
    @IsScalarTower k (RatFunc k) (LaurentSeries k)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro c
  change algebraMap k (LaurentSeries k) c =
    algebraMap (RatFunc k) (LaurentSeries k) (algebraMap k (RatFunc k) c)
  rw [RatFunc.algebraMap_eq_C]
  change algebraMap k (LaurentSeries k) c = ((RatFunc.C c : RatFunc k) : LaurentSeries k)
  rw [RatFunc.coe_C, LaurentSeries.algebraMap_apply]

/-- The actual Laurent derivative agrees with polynomial differentiation. -/
theorem stage14_laurentOrdinaryDerivation_polynomial (p : Polynomial k) :
    laurentOrdinaryDerivation (algebraMap (Polynomial k) (LaurentSeries k) p) =
      algebraMap (Polynomial k) (LaurentSeries k) p.derivative := by
  rw [Polynomial.algebraMap_hahnSeries_apply, laurentOrdinaryDerivation_ofPowerSeries,
    PowerSeries.derivative_coe, Polynomial.algebraMap_hahnSeries_apply]

/-- The actual rational and Laurent derivatives commute with the actual
rational-function inclusion. -/
theorem stage14_rationalLaurent_differential (b : RatFunc k) :
    laurentOrdinaryDerivation (algebraMap (RatFunc k) (LaurentSeries k) b) =
      algebraMap (RatFunc k) (LaurentSeries k) (stage14_rationalOrdinaryDerivation b) :=
  stage14_rationalOrdinaryDerivation_compatible laurentOrdinaryDerivation
    stage14_laurentOrdinaryDerivation_polynomial b

/-- Polynomial ODE closure for the sum of actual Laurent series. -/
theorem stage14_laurentPolynomialODE_add {f g : LaurentSeries k}
    (hf : HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k)) f)
    (hg : HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k)) g) :
    HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k)) (f + g) := by
  letI : SMul k (LaurentSeries k) := Algebra.toSMul
  letI : SMul k (RatFunc k) := Algebra.toSMul
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : Module k (RatFunc k) := Algebra.toModule
  letI : IsScalarTower k (RatFunc k) (LaurentSeries k) := stage14_rationalLaurentScalarTower
  exact polynomialScalarDifferentialRelation_add (k := k) (R := LaurentSeries k)
    (stage14_rationalOrdinaryDerivation (k := k))
    stage14_laurentAlgebraDerivation
    (fun b => stage14_rationalLaurent_differential (k := k) b) hf hg

/-- Polynomial ODE closure for the product of actual Laurent series. -/
theorem stage14_laurentPolynomialODE_mul {f g : LaurentSeries k}
    (hf : HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k)) f)
    (hg : HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k)) g) :
    HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k)) (f * g) := by
  letI : SMul k (LaurentSeries k) := Algebra.toSMul
  letI : SMul k (RatFunc k) := Algebra.toSMul
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : Module k (RatFunc k) := Algebra.toModule
  letI : IsScalarTower k (RatFunc k) (LaurentSeries k) := stage14_rationalLaurentScalarTower
  exact polynomialScalarDifferentialRelation_mul (k := k) (R := LaurentSeries k)
    (stage14_rationalOrdinaryDerivation (k := k))
    stage14_laurentAlgebraDerivation
    (fun b => stage14_rationalLaurent_differential (k := k) b) hf hg
end StrictEUnit
