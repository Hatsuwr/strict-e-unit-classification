import Stage17ConstructedFormalFundamental

/-!
# Evaluation only on a genuinely realized Laurent-log algebra

The coefficient ring is a localization of actual arithmetic entire functions
whose denominators do not vanish off zero. Its polynomial-log algebra embeds
injectively into the formal ambient field. Evaluation at (1,0) is defined on
this realized algebra only, never on arbitrary Laurent series or rational-log
functions.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance (k : Subfield ℂ) : Module (subfieldEntireFunctionAlgebra k) (subfieldEntireFunctionAlgebra k) :=
  @Semiring.toModule _ (subfieldEntireFunctionAlgebra k).toSemiring

local instance (k : Subfield ℂ) : DistribMulAction (subfieldEntireFunctionAlgebra k) (subfieldEntireFunctionAlgebra k) :=
  (@Semiring.toModule _ (subfieldEntireFunctionAlgebra k).toSemiring).toDistribMulAction

attribute [local instance] stage16LocalizationCommMonoid stage16LocalizationAddCommMonoid
  stage16LocalizationAddZeroClass stage16LocalizationAlgebra stage16SourceAlgebra
  stage16SourceSMul stage16SourceModule stage16LocalizationKAlgebra
  stage16LocalizationSourceSMul stage16LocalizationKSMul stage16LocalizationScalarTower

/-- Finite Laurent homomorphisms are determined by constants and the coordinate. -/
theorem stage21_laurentHom_ext {k R : Type*} [Field k] [CommRing R]
    (f g : LaurentPolynomial k →+* R)
    (hC : ∀ c, f (LaurentPolynomial.C c) = g (LaurentPolynomial.C c))
    (ht : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have hti : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    apply ((LaurentPolynomial.isUnit_T (R := k) 1).map f).mul_left_cancel
    rw [← map_mul, ← LaurentPolynomial.T_add]
    rw [ht, ← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on with
  | h_C a => exact hC a
  | h_add hp hq => simp only [map_add, hp, hq]
  | h_C_mul_T n a ih =>
    rw [LaurentPolynomial.T_add, ← mul_assoc, map_mul f, map_mul g, ih, ht]
  | h_C_mul_T_Z n a ih =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc, map_mul f, map_mul g, ih, hti]

abbrev Stage21ActualLocalization (k : Subfield ℂ) :=
  Stage16EntireLocalization k (stage16_puncturedDenominators k)

local instance (k : Subfield ℂ) : CommRing (Stage21ActualLocalization k) :=
  @OreLocalization.instCommRing _ (subfieldEntireFunctionAlgebra k).toCommRing
    (stage16_puncturedDenominators k) inferInstance

local instance (k : Subfield ℂ) : Module k (Stage21ActualLocalization k) :=
  @Algebra.toModule k (Stage21ActualLocalization k) inferInstance inferInstance
    (stage16LocalizationKAlgebra k (stage16_puncturedDenominators k))

def stage21_localizedFormal (k : Subfield ℂ) :
    Stage21ActualLocalization k →ₐ[k] LaurentSeries k :=
  stage16_localizedLaurentAlgHom k (stage16_puncturedDenominators k) le_rfl

def stage21_localizedValueOne (k : Subfield ℂ) :
    Stage21ActualLocalization k →ₐ[k] ℂ where
  toFun q := stage16_localizedPuncturedAlgHom k (stage16_puncturedDenominators k)
    le_rfl q ⟨1, one_ne_zero⟩
  map_zero' := by simp
  map_one' := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  commutes' _ := by simp

@[simp] theorem stage21_localizedValueOne_entire (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    stage21_localizedValueOne k
      (algebraMap (subfieldEntireFunctionAlgebra k) (Stage21ActualLocalization k) f) =
      stage14_subfieldEntireEvaluation k 1 f := by
  change stage16_localizedPuncturedAlgHom k (stage16_puncturedDenominators k) le_rfl
    (algebraMap (subfieldEntireFunctionAlgebra k) (Stage21ActualLocalization k) f)
      ⟨1, one_ne_zero⟩ = _
  rw [stage16_localizedPunctured_algebraMap]
  rfl

def stage21_localizedCoordinateUnit (k : Subfield ℂ) : (Stage21ActualLocalization k)ˣ :=
  (IsLocalization.map_units (Stage21ActualLocalization k)
    (⟨subfieldEntireCoordinate k, stage16_coordinate_mem_denominators k⟩ :
      stage16_puncturedDenominators k)).unit

@[simp] theorem stage21_localizedCoordinateUnit_val (k : Subfield ℂ) :
    (stage21_localizedCoordinateUnit k : Stage21ActualLocalization k) =
      algebraMap (subfieldEntireFunctionAlgebra k) (Stage21ActualLocalization k)
        (subfieldEntireCoordinate k) :=
  (IsLocalization.map_units (Stage21ActualLocalization k)
    (⟨subfieldEntireCoordinate k, stage16_coordinate_mem_denominators k⟩ :
      stage16_puncturedDenominators k)).unit_spec

def stage21_laurentToLocalization (k : Subfield ℂ) :
    LaurentPolynomial k →+* Stage21ActualLocalization k :=
  LaurentPolynomial.eval₂ (algebraMap k (Stage21ActualLocalization k))
    (stage21_localizedCoordinateUnit k)

/-- This actual Laurent realization agrees with the fixed formal embedding. -/
theorem stage21_localizedFormal_laurent (k : Subfield ℂ) (p : LaurentPolynomial k) :
    stage21_localizedFormal k (stage21_laurentToLocalization k p) =
      laurentPolynomialToSeries p := by
  have hh : (stage21_localizedFormal k).toRingHom.comp (stage21_laurentToLocalization k) =
      laurentPolynomialToSeries.toRingHom := by
    apply stage21_laurentHom_ext
    · intro c
      change stage21_localizedFormal k
        (LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C c)) = _
      rw [LaurentPolynomial.eval₂_C, AlgHom.commutes]
      exact (laurentPolynomialToSeries.commutes c).symm
    · change stage21_localizedFormal k
        (LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T (1 : ℤ))) = _
      rw [show (1 : ℤ) = (1 : ℕ) by rfl, LaurentPolynomial.eval₂_T_n, pow_one,
        stage21_localizedCoordinateUnit_val]
      rw [stage21_localizedFormal, stage16_localizedLaurent_algebraMap,
        stage17_entireLaurent_coordinate]
      exact (laurentPolynomialToSeries_single 1 1).symm
  exact RingHom.congr_fun hh p

/-- Its value at one is the actual finite Laurent evaluation. -/
theorem stage21_localizedValueOne_laurent (k : Subfield ℂ) (p : LaurentPolynomial k) :
    stage21_localizedValueOne k (stage21_laurentToLocalization k p) =
      (laurentEvaluateOne k p : ℂ) := by
  have hh : (stage21_localizedValueOne k).toRingHom.comp (stage21_laurentToLocalization k) =
      k.subtype.comp (laurentEvaluateOne k).toRingHom := by
    apply stage21_laurentHom_ext
    · intro c
      change stage21_localizedValueOne k
        (LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C c)) = _
      rw [LaurentPolynomial.eval₂_C, AlgHom.commutes]
      change (c : ℂ) = ((laurentEvaluateOne k) (algebraMap k (LaurentPolynomial k) c) : ℂ)
      rw [AlgHom.commutes]
      rfl
    · change stage21_localizedValueOne k
        (LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T (1 : ℤ))) = _
      rw [show (1 : ℤ) = (1 : ℕ) by rfl, LaurentPolynomial.eval₂_T_n, pow_one,
        stage21_localizedCoordinateUnit_val, stage21_localizedValueOne_entire]
      change (1 : ℂ) = ((laurentEvaluateOne k) (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) : ℂ)
      rw [laurentEvaluateOne_single]
      rfl
  exact RingHom.congr_fun hh p

/-- Actual entire coefficients are embedded as constant log polynomials. -/
def stage21_entireToRealizedLog (k : Subfield ℂ) :
    subfieldEntireFunctionAlgebra k →+* Polynomial (Stage21ActualLocalization k) :=
  Polynomial.C.comp (algebraMap (subfieldEntireFunctionAlgebra k) (Stage21ActualLocalization k))

/-- Finite Laurent-log base elements have genuine localized coefficients. -/
def stage21_baseToRealizedLog (k : Subfield ℂ) :
    LaurentLogBase k →+* Polynomial (Stage21ActualLocalization k) :=
  Polynomial.mapRingHom (stage21_laurentToLocalization k)

/-- Injective formal realization of this particular polynomial-log algebra. -/
def stage21_realizedLogFormal (k : Subfield ℂ) :
    Polynomial (Stage21ActualLocalization k) →+* RatFunc (LaurentSeries k) :=
  (algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))).comp
    (Polynomial.mapRingHom (stage21_localizedFormal k).toRingHom)

theorem stage21_realizedLogFormal_injective (k : Subfield ℂ) :
    Function.Injective (stage21_realizedLogFormal k) :=
  (IsFractionRing.injective (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))).comp
    (Polynomial.map_injective (stage21_localizedFormal k).toRingHom
      (stage16_localizedLaurentAlgHom_injective k (stage16_puncturedDenominators k) le_rfl))

/-- Actual evaluation at (1,0) on the realized algebra, not on the ambient field. -/
def stage21_realizedLogValueOne (k : Subfield ℂ) :
    Polynomial (Stage21ActualLocalization k) →+* ℂ :=
  Polynomial.eval₂RingHom (stage21_localizedValueOne k).toRingHom 0

@[simp] theorem stage21_realizedLogFormal_entire (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    stage21_realizedLogFormal k (stage21_entireToRealizedLog k f) =
      stage17_entireFormalAlgHom k f := by
  change algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
    ((Polynomial.C (algebraMap _ _ f)).map (stage21_localizedFormal k).toRingHom) = _
  rw [Polynomial.map_C]
  change RatFunc.C (stage21_localizedFormal k (algebraMap _ _ f)) = _
  rw [stage21_localizedFormal, stage16_localizedLaurent_algebraMap]
  rfl

@[simp] theorem stage21_realizedLogValueOne_entire (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    stage21_realizedLogValueOne k (stage21_entireToRealizedLog k f) =
      stage14_subfieldEntireEvaluation k 1 f := by
  change (Polynomial.C (algebraMap _ _ f)).eval₂ (stage21_localizedValueOne k).toRingHom 0 = _
  rw [Polynomial.eval₂_C]
  exact stage21_localizedValueOne_entire k f

/-- The formal realization square commutes on every actual base element. -/
@[simp] theorem stage21_realizedLogFormal_base (k : Subfield ℂ)
    (p : LaurentLogBase k) :
    stage21_realizedLogFormal k (stage21_baseToRealizedLog k p) =
      formalBaseEmbedding p := by
  change algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
    ((p.map (stage21_laurentToLocalization k)).map (stage21_localizedFormal k).toRingHom) = _
  rw [Polynomial.map_map]
  have hh : (stage21_localizedFormal k).toRingHom.comp (stage21_laurentToLocalization k) =
      laurentPolynomialToSeries.toRingHom := by
    apply RingHom.ext
    intro q
    exact stage21_localizedFormal_laurent k q
  rw [hh]
  rfl

/-- Actual evaluation agrees with the algebraic base point on the same base. -/
@[simp] theorem stage21_realizedLogValueOne_base (k : Subfield ℂ)
    (p : LaurentLogBase k) :
    stage21_realizedLogValueOne k (stage21_baseToRealizedLog k p) =
      (laurentLogBasePoint k p : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [(stage21_baseToRealizedLog k).map_add, (stage21_realizedLogValueOne k).map_add,
        hp, hq]
      exact (congrArg (fun x : k => (x : ℂ)) ((laurentLogBasePoint k).map_add p q)).symm
  | monomial j a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, laurentLogBasePoint_C, laurentLogBasePoint_X]
    have hC : stage21_realizedLogValueOne k
        (stage21_baseToRealizedLog k (Polynomial.C a)) = (laurentEvaluateOne k a : ℂ) := by
      change ((Polynomial.C a).map (stage21_laurentToLocalization k)).eval₂
        (stage21_localizedValueOne k).toRingHom 0 = _
      rw [Polynomial.map_C, Polynomial.eval₂_C]
      exact stage21_localizedValueOne_laurent k a
    have hX : stage21_realizedLogValueOne k
        (stage21_baseToRealizedLog k Polynomial.X) = 0 := by
      change (Polynomial.X.map (stage21_laurentToLocalization k)).eval₂
        (stage21_localizedValueOne k).toRingHom 0 = 0
      rw [Polynomial.map_X, Polynomial.eval₂_X]
    rw [hC, hX]
    rfl

end StrictEUnit
