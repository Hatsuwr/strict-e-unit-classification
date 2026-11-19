import V5LocalTaylorAlgebra
import V5WidePointedFundamental

noncomputable section
open scoped Topology
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

theorem v5LocalTaylor_id_one : v5LocalTaylor (fun z : ℂ => z) 1 = 1 + PowerSeries.X := by
  apply v5LocalTaylor_eq_of_series analyticAt_id
  apply hasFPowerSeriesAt_iff.mpr
  apply Filter.Eventually.of_forall
  intro z
  have h := (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).add (hasSum_ite_eq (1 : ℕ) z)
  convert h using 1
  funext n
  simp only [FormalMultilinearSeries.coeff_ofScalars, map_add, PowerSeries.coeff_one,
    PowerSeries.coeff_X, smul_eq_mul, mul_add]
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [h1]
  · simp [h0, h1]

/-- A globally nonzero representative of the coordinate germ at 1. -/
def v5LocalCoordinate (z : ℂ) : ℂ := if z = 0 then 1 else z

theorem v5LocalCoordinate_germ : v5LocalCoordinate =ᶠ[𝓝 (1 : ℂ)] (fun z => z) := by
  filter_upwards [isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with z hz
  simp [v5LocalCoordinate, hz]

theorem v5LocalCoordinate_analytic : AnalyticAt ℂ v5LocalCoordinate 1 :=
  analyticAt_id.congr v5LocalCoordinate_germ.symm

def v5LocalCoordinateUnit : (v5LocalAnalyticAlgebra 1)ˣ where
  val := ⟨v5LocalCoordinate, v5LocalCoordinate_analytic⟩
  inv := ⟨fun z => (v5LocalCoordinate z)⁻¹, v5LocalCoordinate_analytic.inv (by simp [v5LocalCoordinate])⟩
  val_inv := by ext z; simp [v5LocalCoordinate]; split_ifs <;> simp_all
  inv_val := by ext z; simp [v5LocalCoordinate]; split_ifs <;> simp_all

theorem v5LocalCoordinateUnit_taylor :
    Units.map (v5LocalTaylorAlgHom 1).toMonoidHom v5LocalCoordinateUnit = v5WidePointedParameter ℂ := by
  apply Units.ext
  change v5LocalTaylor v5LocalCoordinate 1 = 1 + PowerSeries.X
  rw [← v5LocalTaylor_id_one]
  exact (v5LocalTaylor_eq_iff_eventuallyEq v5LocalCoordinate_analytic analyticAt_id).mpr v5LocalCoordinate_germ

def v5LocalLaurentEval {K : Type*} [Field K] (ι : K →+* ℂ) :
    LaurentPolynomial K →+* v5LocalAnalyticAlgebra 1 :=
  LaurentPolynomial.eval₂ ((algebraMap ℂ (v5LocalAnalyticAlgebra 1)).comp ι) v5LocalCoordinateUnit

theorem v5LocalLaurentEval_taylor_complex (p : LaurentPolynomial ℂ) :
    v5LocalTaylorAlgHom 1 (v5LocalLaurentEval (RingHom.id ℂ) p) = v5WidePointedBase ℂ p := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [(v5LocalLaurentEval (RingHom.id ℂ)).map_add, map_add (v5LocalTaylorAlgHom 1),
      map_add (v5WidePointedBase ℂ), ha, hb]
  | C_mul_T n a =>
    simp only [v5LocalLaurentEval, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, RingHom.comp_apply,
      RingHom.id_apply, map_mul, AlgHom.commutes, v5WidePointedBase_C, v5WidePointedBase_T]
    congr 1
    change (Units.map (v5LocalTaylorAlgHom 1).toMonoidHom (v5LocalCoordinateUnit ^ n)).val = _
    rw [map_zpow, v5LocalCoordinateUnit_taylor]

theorem v5WidePointedParameter_map {K : Type*} [Field K] (ι : K →+* ℂ) :
    Units.map (PowerSeries.map ι).toMonoidHom (v5WidePointedParameter K) =
      v5WidePointedParameter ℂ := by
  apply Units.ext
  change PowerSeries.map ι (1 + PowerSeries.X) = 1 + PowerSeries.X
  simp

theorem v5LocalLaurentEval_taylor {K : Type*} [Field K] (ι : K →+* ℂ)
    (p : LaurentPolynomial K) :
    v5LocalTaylorAlgHom 1 (v5LocalLaurentEval ι p) =
      PowerSeries.map ι (v5WidePointedBase K p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [(v5LocalLaurentEval ι).map_add, map_add (v5LocalTaylorAlgHom 1),
      map_add (v5WidePointedBase K), map_add (PowerSeries.map ι), ha, hb]
  | C_mul_T n a =>
    simp only [v5LocalLaurentEval, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T, RingHom.comp_apply, map_mul, AlgHom.commutes,
      v5WidePointedBase_C, v5WidePointedBase_T, PowerSeries.map_C]
    congr 1
    change (Units.map (v5LocalTaylorAlgHom 1).toMonoidHom (v5LocalCoordinateUnit ^ n)).val =
      (Units.map (PowerSeries.map ι).toMonoidHom ((v5WidePointedParameter K)^n)).val
    rw [map_zpow, map_zpow, v5LocalCoordinateUnit_taylor, v5WidePointedParameter_map]

/-- The representative agrees with honest Laurent evaluation at every nonzero point. -/
theorem v5LocalLaurentEval_apply {K : Type*} [Field K] (ι : K →+* ℂ)
    (p : LaurentPolynomial K) (z : ℂ) (hz : z ≠ 0) :
    (v5LocalLaurentEval ι p).val z = LaurentPolynomial.eval₂ ι (Units.mk0 z hz) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [(v5LocalLaurentEval ι).map_add, map_add]
    exact congrArg₂ (· + ·) ha hb
  | C_mul_T n a =>
    simp only [v5LocalLaurentEval, LaurentPolynomial.eval₂_C_mul_T]
    change ι a * ((v5LocalCoordinateUnit ^ n).val.val z) = _
    have hh : ((v5LocalCoordinateUnit ^ n).val.val z) = z^n := by
      let ev : v5LocalAnalyticAlgebra 1 →* ℂ :=
        { toFun := fun f => f.val z, map_one' := rfl, map_mul' := fun _ _ => rfl }
      change ((Units.map ev (v5LocalCoordinateUnit ^ n)).val) = _
      rw [map_zpow, Units.val_zpow_eq_zpow_val]
      simp [ev, v5LocalCoordinateUnit, v5LocalCoordinate, hz]
    rw [hh]
    simp

end StrictEUnit
#print axioms StrictEUnit.v5LocalLaurentEval_taylor_complex

#print axioms StrictEUnit.v5LocalLaurentEval_taylor
#print axioms StrictEUnit.v5LocalLaurentEval_apply
