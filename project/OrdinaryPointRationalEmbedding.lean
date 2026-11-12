import Stage14LaurentPolynomialODEClosure
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
Polynomial translation X ↦ X+β, followed by localization into Laurent series.
Only POLYNOMIAL substitution is used. No substitution of an infinite power
series at a nonzero constant is defined or assumed.
-/
noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The genuine polynomial automorphism, with its inverse already supplied
by the polynomial algebra equivalence. -/
def ordinaryPointPolynomialShift (β : K) : Polynomial K ≃ₐ[K] Polynomial K :=
  Polynomial.algEquivAevalXAddC β

@[simp] theorem ordinaryPointPolynomialShift_apply (β : K) (p : Polynomial K) :
    ordinaryPointPolynomialShift β p = p.comp (Polynomial.X + Polynomial.C β) := rfl

theorem ordinaryPointPolynomialShift_natDegree (β : K) (p : Polynomial K) :
    (ordinaryPointPolynomialShift β p).natDegree = p.natDegree := by
  rw [ordinaryPointPolynomialShift_apply, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_add_C, mul_one]

/-- The actual translated polynomial, in the standard Laurent coefficient field. -/
def ordinaryPointPolynomialMap (β : K) : Polynomial K →+* LaurentSeries K :=
  (algebraMap (Polynomial K) (LaurentSeries K)).comp
    (ordinaryPointPolynomialShift β).toRingEquiv.toRingHom

@[simp] theorem ordinaryPointPolynomialMap_apply (β : K) (p : Polynomial K) :
    ordinaryPointPolynomialMap β p =
      algebraMap (Polynomial K) (LaurentSeries K) (ordinaryPointPolynomialShift β p) := rfl

theorem ordinaryPointPolynomialMap_injective (β : K) :
    Function.Injective (ordinaryPointPolynomialMap β) :=
  (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).comp
    (ordinaryPointPolynomialShift β).injective

/-- Localization of the actual injective shifted polynomial map. -/
def ordinaryPointRationalMap (β : K) : RatFunc K →+* LaurentSeries K :=
  RatFunc.liftRingHom (ordinaryPointPolynomialMap β)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (ordinaryPointPolynomialMap_injective β))

@[simp] theorem ordinaryPointRationalMap_polynomial (β : K) (p : Polynomial K) :
    ordinaryPointRationalMap β (algebraMap (Polynomial K) (RatFunc K) p) =
      ordinaryPointPolynomialMap β p := by
  simpa only [map_one, div_one] using
    (RatFunc.liftRingHom_apply_div (ordinaryPointPolynomialMap β)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (ordinaryPointPolynomialMap_injective β)) p 1)

theorem ordinaryPointRationalMap_injective (β : K) :
    Function.Injective (ordinaryPointRationalMap β) :=
  (ordinaryPointRationalMap β).injective

/-- The coefficient field is fixed, rather than replaced by a new constant field. -/
@[simp] theorem ordinaryPointRationalMap_constant (β c : K) :
    ordinaryPointRationalMap β (algebraMap K (RatFunc K) c) =
      algebraMap K (LaurentSeries K) c := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) c]
  change ordinaryPointRationalMap β
    (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)) = _
  rw [ordinaryPointRationalMap_polynomial, ordinaryPointPolynomialMap_apply,
    ordinaryPointPolynomialShift_apply, Polynomial.C_comp,
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C]
  simpa only [LaurentSeries.algebraMap_apply] using (PowerSeries.coe_C c)

/-- Bundle the same map with its proved constant compatibility. -/
def ordinaryPointRationalAlgHom (β : K) : RatFunc K →ₐ[K] LaurentSeries K where
  __ := ordinaryPointRationalMap β
  commutes' := ordinaryPointRationalMap_constant β

theorem ordinaryPointRationalMap_eq_constant_iff (β c : K) (q : RatFunc K) :
    ordinaryPointRationalMap β q = algebraMap K (LaurentSeries K) c ↔
      q = algebraMap K (RatFunc K) c := by
  rw [← ordinaryPointRationalMap_constant β c]
  exact (ordinaryPointRationalMap_injective β).eq_iff

/-- The chain rule has derivative one for X+β. -/
theorem ordinaryPointPolynomialMap_derivative (β : K) (p : Polynomial K) :
    laurentOrdinaryDerivation (ordinaryPointPolynomialMap β p) =
      ordinaryPointPolynomialMap β p.derivative := by
  rw [ordinaryPointPolynomialMap_apply, stage14_laurentOrdinaryDerivation_polynomial,
    ordinaryPointPolynomialMap_apply]
  congr 1
  simp only [ordinaryPointPolynomialShift_apply, Polynomial.derivative_comp,
    Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
    add_zero, one_mul]

/-- Quotient differentiation transports the actual ordinary rational derivative
through the SAME translated embedding. No differential compatibility is assumed. -/
theorem ordinaryPointRationalMap_derivative (β : K) (q : RatFunc K) :
    laurentOrdinaryDerivation (ordinaryPointRationalMap β q) =
      ordinaryPointRationalMap β (stage14_rationalOrdinaryDerivation q) := by
  induction q using RatFunc.induction_on
  rename_i p q hq
  rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div,
    stage14_rationalOrdinaryDerivation_polynomial,
    stage14_rationalOrdinaryDerivation_polynomial]
  simp only [ordinaryPointRationalMap_polynomial, ordinaryPointPolynomialMap_derivative,
    smul_eq_mul, map_sub, map_mul, map_pow, map_div₀, map_inv₀]

end StrictEUnit
end
