import Stage17ArithmeticPowerPullback

/-! Genuine normalized Euler compatibility of the actual arithmetic Taylor map. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

/-- The literal actual entire-to-formal-ambient map. -/
def stage17_entireFormalAlgHom (k : Subfield ℂ) :
    subfieldEntireFunctionAlgebra k →ₐ[k] RatFunc (LaurentSeries k) :=
  { RatFunc.C.comp (stage14_subfieldEntireLaurentAlgHom k).toRingHom with
    commutes' := fun c => by
      change RatFunc.C (stage14_subfieldEntireLaurentAlgHom k
        (algebraMap k (subfieldEntireFunctionAlgebra k) c)) = _
      rw [(stage14_subfieldEntireLaurentAlgHom k).commutes,
        RatFunc.algebraMap_apply, map_one, div_one]
      rfl }

@[simp] theorem stage17_entireFormalAlgHom_apply (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    stage17_entireFormalAlgHom k f =
      RatFunc.C (stage14_subfieldEntireLaurentAlgHom k f) := rfl

theorem stage17_entireFormalAlgHom_injective (k : Subfield ℂ) :
    Function.Injective (stage17_entireFormalAlgHom k) :=
  (RatFunc.C : LaurentSeries k →+* RatFunc (LaurentSeries k)).injective.comp
    (stage14_subfieldEntireLaurentAlgHom_injective k)

/-- Euler differentiation is coordinate times ordinary differentiation. -/
theorem stage17_laurentEuler_eq_coordinate_mul_derivative {k : Type*} [Field k]
    (a : LaurentSeries k) :
    laurentEuler a = HahnSeries.single (1 : ℤ) (1 : k) * laurentOrdinaryDerivation a := by
  change laurentEuler a = HahnSeries.single (1 : ℤ) (1 : k) *
    (HahnSeries.single (-1 : ℤ) (1 : k) * laurentEuler a)
  rw [← mul_assoc, HahnSeries.single_mul_single]
  norm_num

/-- The embedded actual coordinate is the formal Laurent monomial t. -/
@[simp] theorem stage17_entireLaurent_coordinate (k : Subfield ℂ) :
    stage14_subfieldEntireLaurentAlgHom k (subfieldEntireCoordinate k) =
      HahnSeries.single (1 : ℤ) (1 : k) := by
  rw [stage14_subfieldEntireLaurentAlgHom_apply, subfieldEntireTaylorAlgHom_coordinate,
    HahnSeries.ofPowerSeries_X]

/-- The formal ambient derivation restricts to its specified scaled Laurent
Euler derivative on the actual coefficient field. -/
theorem stage17_formalAmbientDerivation_C {k : Type*} [Field k] [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (a : LaurentSeries k) :
    formalAmbientDerivation N hN (RatFunc.C a) =
      algebraMap k (RatFunc (LaurentSeries k)) (N : k)⁻¹ * RatFunc.C (laurentEuler a) := by
  change seriesRationalScalar (N : k)⁻¹ *
    logRationalDerivation (N : k) (RatFunc.C a) = _
  rw [seriesRationalScalar_eq_algebraMap]
  congr 1
  exact logRationalDerivation_C (N : k) a

/-- Exact Taylor transfer of an actual Euler derivative. -/
theorem stage17_entireFormal_euler (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) :
    formalAmbientDerivation N hN (stage17_entireFormalAlgHom k f) =
      algebraMap k (RatFunc (LaurentSeries k)) (N : k)⁻¹ *
        stage17_entireFormalAlgHom k
          (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k f) := by
  rw [stage17_entireFormalAlgHom_apply, stage17_formalAmbientDerivation_C,
    stage17_laurentEuler_eq_coordinate_mul_derivative,
    ← stage14_subfieldEntireLaurentAlgHom_derivation,
    ← stage17_entireLaurent_coordinate, ← map_mul]
  rfl

/-- The ramified actual Taylor map satisfies D_N Taylor(f(t^N)) =
Taylor((z f′)(t^N)), with no supplied formal differential identity. -/
theorem stage17_entireFormal_powerPullback_derivation (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (f : subfieldEntireFunctionAlgebra k) :
    formalAmbientDerivation N hN (stage17_entireFormalAlgHom k
      (stage17_arithmeticPowerPullback k N hN f)) =
      stage17_entireFormalAlgHom k (stage17_arithmeticPowerPullback k N hN
        (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k f)) := by
  rw [stage17_entireFormal_euler, stage17_arithmeticPowerPullback_euler,
    map_mul, map_natCast]
  have hn : (N : RatFunc (LaurentSeries k)) ≠ 0 := by
    rw [← map_natCast (algebraMap k (RatFunc (LaurentSeries k)))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hN)
  rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end StrictEUnit
