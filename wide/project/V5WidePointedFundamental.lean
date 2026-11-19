import V5ActualWideLaurentSystem
import FormalFundamentalMatrixUnit
import OrdinaryPointLaurentFundamental
import OrdinaryPointFundamentalCoefficients

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable (K : Type*) [Field K]

/-- The original coordinate z represented at the fixed point z=1; X is z-1. -/
def v5WidePointedParameter : (PowerSeries K)ˣ :=
  Units.mkOfMulEqOne (1 + PowerSeries.X) (1 + PowerSeries.X)⁻¹
    (PowerSeries.mul_inv_cancel _ (by simp))

@[simp] theorem v5WidePointedParameter_val :
    (v5WidePointedParameter K : PowerSeries K) = 1 + PowerSeries.X := rfl

/-- Literal translation of the Laurent coefficient ring at 1. -/
def v5WidePointedBase : LaurentPolynomial K →ₐ[K] PowerSeries K :=
  { LaurentPolynomial.eval₂ (PowerSeries.C K) (v5WidePointedParameter K) with
    commutes' := by intro c; exact LaurentPolynomial.eval₂_C _ _ c }

@[simp] theorem v5WidePointedBase_C (c : K) :
    v5WidePointedBase K (LaurentPolynomial.C c) = PowerSeries.C K c := by
  exact LaurentPolynomial.eval₂_C _ _ c

@[simp] theorem v5WidePointedBase_T (n : ℤ) :
    v5WidePointedBase K (LaurentPolynomial.T n) = ((v5WidePointedParameter K)^n).val := by
  exact LaurentPolynomial.eval₂_T _ _ n

@[simp] theorem v5WidePointedParameter_constant :
    Units.map (PowerSeries.constantCoeff K).toMonoidHom (v5WidePointedParameter K) = 1 := by
  apply Units.ext
  simp

/-- Specialization of the translated coefficients is exactly z=1, not a
freely chosen ordinary point. -/
theorem v5WidePointedBase_constant (p : LaurentPolynomial K) :
    PowerSeries.constantCoeff K (v5WidePointedBase K p) =
      LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T n c =>
    simp only [map_mul, v5WidePointedBase_C, v5WidePointedBase_T,
      PowerSeries.constantCoeff_C, LaurentPolynomial.eval₂_C, RingHom.id_apply,
      LaurentPolynomial.eval₂_T]
    have h : PowerSeries.constantCoeff K ((v5WidePointedParameter K)^n).val = 1 := by
      change (Units.map (PowerSeries.constantCoeff K).toMonoidHom
        ((v5WidePointedParameter K)^n)).val = 1
      rw [map_zpow, v5WidePointedParameter_constant, one_zpow]
      rfl
    simp only [h, mul_one, one_zpow, Units.val_one]


/-- Translation agrees with the fixed ordinary-point polynomial embedding. -/
theorem v5WidePointedBase_toLaurent (p : Polynomial K) :
    v5WidePointedBase K p.toLaurent = ordinaryPointPolynomialSeries 1 p := by
  have h : (v5WidePointedBase K).toRingHom.comp Polynomial.toLaurent =
      ordinaryPointPolynomialSeriesHom (1 : K) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [ordinaryPointPolynomialSeriesHom, ordinaryPointPolynomialSeries,
        ordinaryPointPolynomialShift_apply]
    · simp [ordinaryPointPolynomialSeriesHom, ordinaryPointPolynomialSeries,
        ordinaryPointPolynomialShift_apply, v5WidePointedParameter, add_comm]
  exact congrArg (fun f : Polynomial K →+* PowerSeries K => f p) h

/-- The translated coefficient map is faithful: no Laurent coefficient is lost. -/
theorem v5WidePointedBase_injective : Function.Injective (v5WidePointedBase K) := by
  apply (injective_iff_map_eq_zero (v5WidePointedBase K)).2
  intro p hp
  obtain ⟨n,q,hq⟩ := LaurentPolynomial.exists_T_pow p
  have hq0 : ordinaryPointPolynomialSeries (1 : K) q = 0 := by
    rw [← v5WidePointedBase_toLaurent, hq, map_mul, hp, zero_mul]
  have hq' : q = 0 := by
    apply ordinaryPointPolynomialMap_injective (1 : K)
    simpa only [map_zero, ← ordinaryPointPolynomialSeries_coe, hq0] using
      (map_zero (HahnSeries.ofPowerSeries ℤ K))
  have hz : p * LaurentPolynomial.T (n : ℤ) = 0 := by
    rw [← hq, hq', map_zero]
  exact (LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_eq_zero.mp hz

variable {K} {r : ℕ}
/-- Constructed normalized fundamental matrix for the supplied Laurent system. -/
def v5WidePointedFundamental
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Matrix (Fin r) (Fin r) (PowerSeries K) :=
  formalFundamentalMatrix (A.map (v5WidePointedBase K))

@[simp] theorem v5WidePointedFundamental_normalized
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (v5WidePointedFundamental A).map (PowerSeries.constantCoeff K) = 1 :=
  formalFundamentalMatrix_constantCoeff _

theorem v5WidePointedFundamental_equation [CharZero K]
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (v5WidePointedFundamental A).map (PowerSeries.derivative K) =
      A.map (v5WidePointedBase K) * v5WidePointedFundamental A :=
  formalFundamentalMatrix_derivative _

@[simp] theorem v5WidePointedFundamental_det_constant
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    PowerSeries.constantCoeff K (v5WidePointedFundamental A).det = 1 :=
  formalFundamentalMatrix_det_constantCoeff _

theorem v5WidePointedFundamental_isUnit
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    IsUnit (v5WidePointedFundamental A) := formalFundamentalMatrix_isUnit _

/-- The same fixed-point Laurent coefficient map, now in the ambient field. -/
def v5WidePointedLaurentBase (K : Type*) [Field K] :
    LaurentPolynomial K →ₐ[K] LaurentSeries K :=
  { (HahnSeries.ofPowerSeries ℤ K).comp (v5WidePointedBase K).toRingHom with
    commutes' := by
      intro c
      change HahnSeries.ofPowerSeries ℤ K (v5WidePointedBase K (LaurentPolynomial.C c)) = _
      rw [v5WidePointedBase_C]
      rfl }

/-- The constructed matrix in the Laurent ambient field, with the power-series
source still available for its algebraic point. -/
def v5WidePointedLaurentFundamental
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Matrix (Fin r) (Fin r) (LaurentSeries K) :=
  (v5WidePointedFundamental A).map (HahnSeries.ofPowerSeries ℤ K)

theorem v5WidePointedLaurentFundamental_isUnit
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    IsUnit (v5WidePointedLaurentFundamental A) :=
  (v5WidePointedFundamental_isUnit A).map (HahnSeries.ofPowerSeries ℤ K).mapMatrix

theorem v5WidePointedLaurentFundamental_equation [CharZero K]
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    ∀ i j, laurentOrdinaryDerivation (v5WidePointedLaurentFundamental A i j) =
      ∑ l, v5WidePointedLaurentBase K (A i l) * v5WidePointedLaurentFundamental A l j := by
  intro i j
  let ψ := HahnSeries.ofPowerSeries ℤ K
  change laurentOrdinaryDerivation (ψ (v5WidePointedFundamental A i j)) = _
  rw [laurentOrdinaryDerivation_ofPowerSeries]
  have hd := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => M i j)
    (v5WidePointedFundamental_equation A)
  change PowerSeries.derivative K (v5WidePointedFundamental A i j) = _ at hd
  dsimp only at hd
  rw [hd, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact map_mul ψ _ _

#print axioms v5WidePointedBase_injective
#print axioms v5WidePointedLaurentFundamental_equation
#print axioms v5WidePointedLaurentFundamental_isUnit

#print axioms v5WidePointedBase_constant
#print axioms v5WidePointedFundamental_equation
#print axioms v5WidePointedFundamental_isUnit
end StrictEUnit
