import Stage14ActualAnalyticODETransfer
import Mathlib.RingTheory.Localization.Basic

/-!
# Actual arithmetic entire functions localized on the punctured plane

Only entire functions with actual Taylor coefficients in the specified subfield
are localized. Every permitted denominator is required to have no zeros off the
origin. The two maps below are constructed, and their injectivity is proved.
The target of the analytic map is the ring of functions on the punctured plane,
not a field and not the ring of all functions on the whole complex plane.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- The actual complex plane with its origin removed. -/
abbrev Stage16PuncturedPlane := {z : ℂ // z ≠ 0}

/-- Restrict an actual arithmetic entire function to the punctured plane. -/
def stage16_entirePuncturedAlgHom (k : Subfield ℂ) :
    subfieldEntireFunctionAlgebra k →ₐ[k] (Stage16PuncturedPlane → ℂ) where
  toFun f z := f.val.val z.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Removing one point does not identify distinct entire functions. Continuity
and the density of the punctured plane provide the value at the missing point. -/
theorem stage16_entirePuncturedAlgHom_injective (k : Subfield ℂ) :
    Function.Injective (stage16_entirePuncturedAlgHom k) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    f.val.property.continuous g.val.property.continuous
  intro z hz
  exact congrFun h ⟨z, hz⟩

/-- The largest denominator submonoid safe at every nonzero complex point. -/
def stage16_puncturedDenominators (k : Subfield ℂ) :
    Submonoid (subfieldEntireFunctionAlgebra k) where
  carrier := {f | ∀ z : Stage16PuncturedPlane, f.val.val z.val ≠ 0}
  one_mem' := by intro z; exact one_ne_zero
  mul_mem' := by intro f g hf hg z; exact mul_ne_zero (hf z) (hg z)

/-- The actual identity coordinate is a permissible denominator. -/
theorem stage16_coordinate_mem_denominators (k : Subfield ℂ) :
    subfieldEntireCoordinate k ∈ stage16_puncturedDenominators k := by
  intro z
  exact z.property

/-- A permissible denominator is nonzero as an actual entire function. -/
theorem stage16_denominator_ne_zero (k : Subfield ℂ)
    (s : stage16_puncturedDenominators k) :
    (s : subfieldEntireFunctionAlgebra k) ≠ 0 := by
  intro h
  have hs := s.property ⟨1, one_ne_zero⟩
  apply hs
  rw [h]
  rfl

/-- A nowhere-zero punctured function is a unit in the pointwise function ring. -/
theorem stage16_punctured_denominator_isUnit (k : Subfield ℂ)
    (s : stage16_puncturedDenominators k) :
    IsUnit (stage16_entirePuncturedAlgHom k s) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨fun z => (s.val.val.val z.val)⁻¹, ?_⟩
  funext z
  exact mul_inv_cancel₀ (s.property z)

/-- Actual Taylor injectivity makes each permitted denominator invertible in
Laurent series. No convergence of arbitrary formal series is being postulated. -/
theorem stage16_laurent_denominator_isUnit (k : Subfield ℂ)
    (s : stage16_puncturedDenominators k) :
    IsUnit (stage14_subfieldEntireLaurentAlgHom k s) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply stage16_denominator_ne_zero k s
  exact stage14_subfieldEntireLaurentAlgHom_injective k
    (h.trans (map_zero (stage14_subfieldEntireLaurentAlgHom k)).symm)

section Localization
variable (k : Subfield ℂ) (M : Submonoid (subfieldEntireFunctionAlgebra k))
    (hM : M ≤ stage16_puncturedDenominators k)

local instance stage16LocalizationCommMonoid :
    CommMonoid (subfieldEntireFunctionAlgebra k) :=
  @CommSemiring.toCommMonoid _ (subfieldEntireFunctionAlgebra k).toCommSemiring

local instance stage16LocalizationAddCommMonoid :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring))

local instance stage16LocalizationAddZeroClass :
    AddZeroClass (subfieldEntireFunctionAlgebra k) :=
  @AddMonoid.toAddZeroClass _ (@AddCommMonoid.toAddMonoid _
    (@NonUnitalNonAssocSemiring.toAddCommMonoid _
      (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
        (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring))))

/-- The genuine localization of the actual arithmetic entire-function algebra. -/
abbrev Stage16EntireLocalization := Localization M

local instance stage16LocalizationAlgebra :
    Algebra (subfieldEntireFunctionAlgebra k) (Stage16EntireLocalization k M) :=
  OreLocalization.instAlgebra

local instance stage16SourceAlgebra : Algebra k (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).algebra

local instance stage16SourceSMul : SMul k (subfieldEntireFunctionAlgebra k) :=
  @Algebra.toSMul k (subfieldEntireFunctionAlgebra k) inferInstance
    (subfieldEntireFunctionAlgebra k).toSemiring (stage16SourceAlgebra k)

local instance stage16SourceModule : Module k (subfieldEntireFunctionAlgebra k) :=
  @Algebra.toModule k (subfieldEntireFunctionAlgebra k) inferInstance
    (subfieldEntireFunctionAlgebra k).toSemiring (stage16SourceAlgebra k)

local instance stage16LocalizationKAlgebra : Algebra k (Stage16EntireLocalization k M) :=
  OreLocalization.instAlgebra (R₀ := k) (R := subfieldEntireFunctionAlgebra k) (S := M)

local instance stage16LocalizationSourceSMul :
    SMul (subfieldEntireFunctionAlgebra k) (Stage16EntireLocalization k M) :=
  @Algebra.toSMul (subfieldEntireFunctionAlgebra k) (Stage16EntireLocalization k M)
    (subfieldEntireFunctionAlgebra k).toCommSemiring inferInstance
    (stage16LocalizationAlgebra k M)

local instance stage16LocalizationKSMul : SMul k (Stage16EntireLocalization k M) :=
  @Algebra.toSMul k (Stage16EntireLocalization k M) inferInstance inferInstance
    (stage16LocalizationKAlgebra k M)

local instance stage16LocalizationScalarTower :
    IsScalarTower k (subfieldEntireFunctionAlgebra k) (Stage16EntireLocalization k M) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := subfieldEntireFunctionAlgebra k)
    (A := Stage16EntireLocalization k M) (fun _ => rfl)

/-- The actual Taylor-to-Laurent map extended to the specified localization. -/
def stage16_localizedLaurentAlgHom :
    Stage16EntireLocalization k M →ₐ[k] LaurentSeries k :=
  IsLocalization.liftAlgHom (A := k) (R := subfieldEntireFunctionAlgebra k)
    (S := Stage16EntireLocalization k M) (M := M) (P := LaurentSeries k)
    (f := stage14_subfieldEntireLaurentAlgHom k) (fun s : M =>
    stage16_laurent_denominator_isUnit k ⟨s.val, hM s.property⟩)

/-- Pointwise evaluation on the actual punctured plane, extended to fractions. -/
def stage16_localizedPuncturedAlgHom :
    Stage16EntireLocalization k M →ₐ[k] (Stage16PuncturedPlane → ℂ) :=
  IsLocalization.liftAlgHom (A := k) (R := subfieldEntireFunctionAlgebra k)
    (S := Stage16EntireLocalization k M) (M := M) (P := Stage16PuncturedPlane → ℂ)
    (f := stage16_entirePuncturedAlgHom k) (fun s : M =>
    stage16_punctured_denominator_isUnit k ⟨s.val, hM s.property⟩)

@[simp] theorem stage16_localizedLaurent_algebraMap
    (f : subfieldEntireFunctionAlgebra k) :
    stage16_localizedLaurentAlgHom k M hM
      (algebraMap (subfieldEntireFunctionAlgebra k) (Stage16EntireLocalization k M) f) =
      stage14_subfieldEntireLaurentAlgHom k f :=
  IsLocalization.lift_eq _ f

@[simp] theorem stage16_localizedPunctured_algebraMap
    (f : subfieldEntireFunctionAlgebra k) :
    stage16_localizedPuncturedAlgHom k M hM
      (algebraMap (subfieldEntireFunctionAlgebra k) (Stage16EntireLocalization k M) f) =
      stage16_entirePuncturedAlgHom k f :=
  IsLocalization.lift_eq _ f

/-- Injectivity of the extended actual Taylor map is a theorem, not a field
embedding or realization hypothesis. -/
theorem stage16_localizedLaurentAlgHom_injective :
    Function.Injective (stage16_localizedLaurentAlgHom k M hM) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro f g
  constructor
  · intro h
    have hh := congrArg (stage16_localizedLaurentAlgHom k M hM) h
    simpa only [stage16_localizedLaurent_algebraMap] using hh
  · intro h
    rw [stage14_subfieldEntireLaurentAlgHom_injective k h]

/-- The punctured analytic realization is injective on this localization. -/
theorem stage16_localizedPuncturedAlgHom_injective :
    Function.Injective (stage16_localizedPuncturedAlgHom k M hM) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro f g
  constructor
  · intro h
    have hh := congrArg (stage16_localizedPuncturedAlgHom k M hM) h
    simpa only [stage16_localizedPunctured_algebraMap] using hh
  · intro h
    rw [stage16_entirePuncturedAlgHom_injective k h]

/-- Every formal fraction is the quotient of its two genuine Taylor series. -/
theorem stage16_localizedLaurent_mk' (f : subfieldEntireFunctionAlgebra k) (s : M) :
    stage16_localizedLaurentAlgHom k M hM
      (IsLocalization.mk' (Stage16EntireLocalization k M) f s) =
      stage14_subfieldEntireLaurentAlgHom k f /
        stage14_subfieldEntireLaurentAlgHom k s := by
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  exact (mul_div_cancel₀ _
    (stage16_laurent_denominator_isUnit k ⟨s.val, hM s.property⟩).ne_zero).symm

/-- The analytic realization evaluates fractions by the actual quotient formula,
with the nonvanishing of the denominator proved from its specified membership. -/
theorem stage16_localizedPunctured_mk' (f : subfieldEntireFunctionAlgebra k)
    (s : M) (z : Stage16PuncturedPlane) :
    stage16_localizedPuncturedAlgHom k M hM
      (IsLocalization.mk' (Stage16EntireLocalization k M) f s) z =
      f.val.val z.val / s.val.val.val z.val := by
  have h : stage16_localizedPuncturedAlgHom k M hM
      (IsLocalization.mk' (Stage16EntireLocalization k M) f s) =
      (fun z => f.val.val z.val / s.val.val.val z.val) := by
    apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
    funext z
    exact (mul_div_cancel₀ _ (hM s.property z)).symm
  exact congrFun h z

end Localization
end StrictEUnit
