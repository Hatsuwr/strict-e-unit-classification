import Stage38CoefficientwiseIndependence
import LaurentLogSeriesEmbedding
import FormalAmbientDifferentialField

/-!
# Literal field extension on power, Laurent, and finite-log series

These maps extract and extend actual coefficients. In particular the
independence theorem applies to K((t))[ell], where log degree is finite but
Laurent series need not have finite support. No analytic evaluation is used.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

/-- All ordinary power-series coefficients as a linear map. -/
def stage38_powerCoefficients : PowerSeries K →ₗ[K] (ℕ → K) where
  toFun f n := PowerSeries.coeff K n f
  map_add' f g := by ext n; exact map_add (PowerSeries.coeff K n) f g
  map_smul' c f := by ext n; exact PowerSeries.coeff_smul n f c

/-- All integer-indexed Laurent coefficients as a linear map. -/
def stage38_laurentCoefficients : LaurentSeries K →ₗ[K] (ℤ → K) where
  toFun := HahnSeries.coeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The log-degree/Laurent-exponent pair extracts a scalar coefficient. -/
def stage38_logCoefficients : Polynomial (LaurentSeries K) →ₗ[K] ((ℕ × ℤ) → K) where
  toFun p j := (p.coeff j.1).coeff j.2
  map_add' p q := by ext j; simp only [Polynomial.coeff_add, HahnSeries.coeff_add, Pi.add_apply]
  map_smul' c p := by ext j; simp only [Polynomial.coeff_smul, HahnSeries.coeff_smul,
    Pi.smul_apply, RingHom.id_apply]

theorem stage38_powerCoefficients_injective :
    Function.Injective (stage38_powerCoefficients (K := K)) := by
  intro f g h
  exact PowerSeries.ext (congrFun h)

theorem stage38_laurentCoefficients_injective :
    Function.Injective (stage38_laurentCoefficients (K := K)) := HahnSeries.coeff_injective

theorem stage38_logCoefficients_injective :
    Function.Injective (stage38_logCoefficients (K := K)) := by
  intro p q h
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  exact congrFun h (j, n)

/-- Coefficient extension is a ring homomorphism on actual Laurent series. -/
def stage38_laurentMap (f : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

omit [Algebra K L] in
@[simp] theorem stage38_laurentMap_coeff (f : K →+* L) (x : LaurentSeries K) (n : ℤ) :
    (stage38_laurentMap f x).coeff n = f (x.coeff n) := rfl

/-- The finite formal logarithm is unchanged by coefficient-field extension. -/
def stage38_logMap (f : K →+* L) :
    Polynomial (LaurentSeries K) →+* Polynomial (LaurentSeries L) :=
  Polynomial.mapRingHom (stage38_laurentMap f)

omit [Algebra K L] in
@[simp] theorem stage38_logMap_coeff (f : K →+* L)
    (p : Polynomial (LaurentSeries K)) (j : ℕ) (n : ℤ) :
    ((stage38_logMap f p).coeff j).coeff n = f ((p.coeff j).coeff n) := by
  change ((p.map (stage38_laurentMap f)).coeff j).coeff n = _
  rw [Polynomial.coeff_map, stage38_laurentMap_coeff]

/-- Ordinary power-series independence survives coefficient extension. -/
theorem stage38_powerSeries_linearIndependent (v : ι → PowerSeries K)
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  exact stage38_linearIndependent_of_extended_coefficients
    stage38_powerCoefficients stage38_powerCoefficients_injective
    stage38_powerCoefficients v _ (fun _ _ => PowerSeries.coeff_map _ _ _) hv

/-- Actual Laurent-series independence survives coefficient extension. -/
theorem stage38_laurentSeries_linearIndependent (v : ι → LaurentSeries K)
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => stage38_laurentMap (algebraMap K L) (v i)) := by
  exact stage38_linearIndependent_of_extended_coefficients
    stage38_laurentCoefficients stage38_laurentCoefficients_injective
    stage38_laurentCoefficients v _ (fun _ _ => rfl) hv

/-- Finite-log Laurent-series independence survives coefficient extension. -/
theorem stage38_logSeries_linearIndependent (v : ι → Polynomial (LaurentSeries K))
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => stage38_logMap (algebraMap K L) (v i)) := by
  exact stage38_linearIndependent_of_extended_coefficients
    stage38_logCoefficients stage38_logCoefficients_injective
    stage38_logCoefficients v _ (fun _ s => stage38_logMap_coeff _ _ s.1 s.2) hv

/-- The polynomial-log inclusion is genuinely L-linear. -/
def stage38_logAmbient : Polynomial (LaurentSeries L) →ₐ[L] RatFunc (LaurentSeries L) :=
  { algebraMap (Polynomial (LaurentSeries L)) (RatFunc (LaurentSeries L)) with
    commutes' := fun c => by
      change algebraMap _ (RatFunc (LaurentSeries L))
        (Polynomial.C (algebraMap L (LaurentSeries L) c)) = _
      rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
      exact seriesRationalScalar_eq_algebraMap c }

theorem stage38_logAmbient_injective :
    Function.Injective (stage38_logAmbient (L := L)) :=
  IsFractionRing.injective (Polynomial (LaurentSeries L)) (RatFunc (LaurentSeries L))

/-- Generic algebra embeddings preserve independence over the unchanged field. -/
theorem stage38_algHom_linearIndependent
    {F A B η : Type*} [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] (f : A →ₐ[F] B)
    (hf : Function.Injective f) (v : η → A) (hv : LinearIndependent F v) :
    LinearIndependent F (fun i => f (v i)) :=
  hv.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr hf)

omit [Algebra K L] in
/-- The coefficientwise and algebraic module structures coincide extensionally.
Making this equality explicit avoids a non-definitional scalar-action diamond. -/
theorem stage38_logModule_eq : (inferInstance : Module L (Polynomial (LaurentSeries L))) =
    (Algebra.toModule : Module L (Polynomial (LaurentSeries L))) := by
  apply Module.ext'
  intro c p
  rw [Algebra.smul_def]
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_smul, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
  exact HahnSeries.single_zero_mul_eq_smul.symm

omit [Algebra K L] in
/-- The injective polynomial inclusion preserves independence over its own field. -/
theorem stage38_logAmbient_linearIndependent
    (v : ι → Polynomial (LaurentSeries L)) (hv : LinearIndependent L v) :
    LinearIndependent L (fun i => stage38_logAmbient (v i)) := by
  have hv' : @LinearIndependent ι L (Polynomial (LaurentSeries L)) v _ _
      (Algebra.toModule : Module L (Polynomial (LaurentSeries L))) := by
    simpa only [stage38_logModule_eq] using hv
  exact stage38_algHom_linearIndependent stage38_logAmbient stage38_logAmbient_injective v hv'

/-- Source-facing endpoint: a K-independent scalar family in K((t))[ell]
remains L-independent in the exact ambient L((t))(ell) used by Stage33. -/
theorem stage38_logSeries_ambient_linearIndependent
    (v : ι → Polynomial (LaurentSeries K)) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => stage38_logAmbient
      (stage38_logMap (algebraMap K L) (v i))) :=
  stage38_logAmbient_linearIndependent _
    (stage38_logSeries_linearIndependent (L := L) v hv)

omit [Algebra K L] in
/-- Coefficient extension commutes with the Euler-plus-log operator, with
its parameter transported literally. This preserves finite differential relations. -/
theorem stage38_logMap_euler (f : K →+* L) (N : K)
    (p : Polynomial (LaurentSeries K)) :
    stage38_logMap f (logPolynomialEuler N p) =
      logPolynomialEuler (f N) (stage38_logMap f p) := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  simp only [stage38_logMap_coeff, logPolynomialEuler_double_coeff,
    map_add, map_mul, map_intCast, map_natCast, map_one]

end StrictEUnit
