import Stage16PuncturedEntireLocalization
import Stage18ArithmeticEntireFractions

/-! Genuine localization of growth-bounded arithmetic entire functions.
The source is a single subalgebra of actual complex functions. Its carrier
requires differentiability, actual Taylor arithmetic, and the proved growth
predicate, avoiding an unnecessary tower of nested function subalgebras. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- Bounded arithmetic entire functions, flattened into one function subalgebra.
Every carrier condition refers to the actual underlying complex function. -/
def stage18_boundedArithmeticEntireAlgebra (k : Subfield ℂ) (N : ℕ) :
    Subalgebra k (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f ∧
    (∀ n, entireCauchyCoefficient f n ∈ k) ∧ HasPowerExponentialBound N f}
  mul_mem' := by
    intro f g hf hg
    refine ⟨hf.1.mul hg.1, ?_, powerExponentialBound_mul N id f g hf.2.2 hg.2.2⟩
    let F : subfieldEntireFunctionAlgebra k :=
      ⟨⟨f, hf.1⟩, (mem_subfieldEntireFunctionAlgebra k _).mpr hf.2.1⟩
    let G : subfieldEntireFunctionAlgebra k :=
      ⟨⟨g, hg.1⟩, (mem_subfieldEntireFunctionAlgebra k _).mpr hg.2.1⟩
    exact (mem_subfieldEntireFunctionAlgebra k (F * G).val).mp (F * G).property
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_, powerExponentialBound_add N id f g hf.2.2 hg.2.2⟩
    let F : subfieldEntireFunctionAlgebra k :=
      ⟨⟨f, hf.1⟩, (mem_subfieldEntireFunctionAlgebra k _).mpr hf.2.1⟩
    let G : subfieldEntireFunctionAlgebra k :=
      ⟨⟨g, hg.1⟩, (mem_subfieldEntireFunctionAlgebra k _).mpr hg.2.1⟩
    exact (mem_subfieldEntireFunctionAlgebra k (F + G).val).mp (F + G).property
  algebraMap_mem' c := by
    refine ⟨differentiable_const (c : ℂ), ?_, powerExponentialBound_const N id (c : ℂ)⟩
    exact (mem_subfieldEntireFunctionAlgebra k
      (algebraMap k entireFunctionAlgebra c)).mp
      ((subfieldEntireFunctionAlgebra k).algebraMap_mem c)

/-- Bundle an existing actual arithmetic entire function with its growth proof. -/
def stage18_boundArithmeticFunction (k : Subfield ℂ) (N : ℕ)
    (f : subfieldEntireFunctionAlgebra k) (hf : HasPowerExponentialBound N f.val.val) :
    stage18_boundedArithmeticEntireAlgebra k N :=
  ⟨f.val.val, f.val.property,
    (mem_subfieldEntireFunctionAlgebra k f.val).mp f.property, hf⟩

@[simp] theorem stage18_boundArithmeticFunction_apply (k : Subfield ℂ) (N : ℕ)
    (f : subfieldEntireFunctionAlgebra k) (hf : HasPowerExponentialBound N f.val.val) (z : ℂ) :
    (stage18_boundArithmeticFunction k N f hf).val z = f.val.val z := rfl

/-- Differentiability is part of the actual bounded source carrier. -/
theorem stage18_bounded_differentiable (k : Subfield ℂ) (N : ℕ)
    (f : stage18_boundedArithmeticEntireAlgebra k N) : Differentiable ℂ f.val :=
  f.property.1

/-- The constructed forgetful map to the existing actual arithmetic entire ring. -/
def stage18_boundedToArithmeticAlgHom (k : Subfield ℂ) (N : ℕ) :
    stage18_boundedArithmeticEntireAlgebra k N →ₐ[k] subfieldEntireFunctionAlgebra k where
  toFun f := ⟨⟨f.val, f.property.1⟩,
    (mem_subfieldEntireFunctionAlgebra k _).mpr f.property.2.1⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem stage18_boundedToArithmeticAlgHom_apply (k : Subfield ℂ) (N : ℕ)
    (f : stage18_boundedArithmeticEntireAlgebra k N) (z : ℂ) :
    (stage18_boundedToArithmeticAlgHom k N f).val.val z = f.val z := rfl

/-- The inherited genuine punctured-function map on the flattened source. -/
def stage18_boundedPuncturedAlgHom (k : Subfield ℂ) (N : ℕ) :
    stage18_boundedArithmeticEntireAlgebra k N →ₐ[k] (Stage16PuncturedPlane → ℂ) :=
  (stage16_entirePuncturedAlgHom k).comp (stage18_boundedToArithmeticAlgHom k N)

/-- The inherited genuine Taylor-to-Laurent map on the flattened source. -/
def stage18_boundedLaurentAlgHom (k : Subfield ℂ) (N : ℕ) :
    stage18_boundedArithmeticEntireAlgebra k N →ₐ[k] LaurentSeries k :=
  (stage14_subfieldEntireLaurentAlgHom k).comp (stage18_boundedToArithmeticAlgHom k N)

/-- Precisely those bounded arithmetic entire functions nonzero off the origin. -/
def stage18_boundedPuncturedDenominators (k : Subfield ℂ) (N : ℕ) :
    Submonoid (stage18_boundedArithmeticEntireAlgebra k N) where
  carrier := {f | ∀ z : Stage16PuncturedPlane, f.val z.val ≠ 0}
  one_mem' := by intro z; exact one_ne_zero
  mul_mem' := by intro f g hf hg z; exact mul_ne_zero (hf z) (hg z)

section Localization
variable (k : Subfield ℂ) (N : ℕ)
    (M : Submonoid (stage18_boundedArithmeticEntireAlgebra k N))
    (hM : M ≤ stage18_boundedPuncturedDenominators k N)

/-- The localization is an actual ring construction over the bounded algebra. -/
abbrev Stage18BoundedArithmeticLocalization := Localization M

/-- Actual analytic evaluation, extended to the genuine localization. -/
def stage18_localizedPuncturedAlgHom :
    Stage18BoundedArithmeticLocalization k N M →ₐ[k] (Stage16PuncturedPlane → ℂ) where
  __ := IsLocalization.lift (M := M) (S := Stage18BoundedArithmeticLocalization k N M)
    (g := (stage18_boundedPuncturedAlgHom k N).toRingHom) (fun s : M =>
    show IsUnit (stage18_boundedPuncturedAlgHom k N s) from
      stage16_punctured_denominator_isUnit k ⟨stage18_boundedToArithmeticAlgHom k N s, hM s.property⟩)
  commutes' c := by
    change IsLocalization.lift _
      (algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage18BoundedArithmeticLocalization k N M)
        (algebraMap k (stage18_boundedArithmeticEntireAlgebra k N) c)) = _
    rw [IsLocalization.lift_eq]
    exact (stage18_boundedPuncturedAlgHom k N).commutes c

/-- Actual Taylor realization, extended to the same genuine localization. -/
def stage18_localizedLaurentAlgHom :
    Stage18BoundedArithmeticLocalization k N M →ₐ[k] LaurentSeries k where
  __ := IsLocalization.lift (M := M) (S := Stage18BoundedArithmeticLocalization k N M)
    (g := (stage18_boundedLaurentAlgHom k N).toRingHom) (fun s : M =>
    show IsUnit (stage18_boundedLaurentAlgHom k N s) from
      stage16_laurent_denominator_isUnit k ⟨stage18_boundedToArithmeticAlgHom k N s, hM s.property⟩)
  commutes' c := by
    change IsLocalization.lift _
      (algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage18BoundedArithmeticLocalization k N M)
        (algebraMap k (stage18_boundedArithmeticEntireAlgebra k N) c)) = _
    rw [IsLocalization.lift_eq]
    exact (stage18_boundedLaurentAlgHom k N).commutes c

@[simp] theorem stage18_localizedPunctured_algebraMap
    (f : stage18_boundedArithmeticEntireAlgebra k N) :
    stage18_localizedPuncturedAlgHom k N M hM
      (algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage18BoundedArithmeticLocalization k N M) f) =
      stage18_boundedPuncturedAlgHom k N f :=
  IsLocalization.lift_eq _ f

@[simp] theorem stage18_localizedLaurent_algebraMap
    (f : stage18_boundedArithmeticEntireAlgebra k N) :
    stage18_localizedLaurentAlgHom k N M hM
      (algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage18BoundedArithmeticLocalization k N M) f) =
      stage18_boundedLaurentAlgHom k N f :=
  IsLocalization.lift_eq _ f

/-- The analytic map is injective, including the removed origin by continuity. -/
theorem stage18_localizedPuncturedAlgHom_injective :
    Function.Injective (stage18_localizedPuncturedAlgHom k N M hM) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro f g
  constructor
  · intro h
    have hh := congrArg (stage18_localizedPuncturedAlgHom k N M hM) h
    simpa only [stage18_localizedPunctured_algebraMap] using hh
  · intro h
    have he0 : stage18_boundedToArithmeticAlgHom k N f =
        stage18_boundedToArithmeticAlgHom k N g :=
      stage16_entirePuncturedAlgHom_injective k h
    have he : f = g := Subtype.ext
      (congrArg (fun a : subfieldEntireFunctionAlgebra k => a.val.val) he0)
    rw [he]

/-- The formal map is injective because it uses actual Taylor coefficients. -/
theorem stage18_localizedLaurentAlgHom_injective :
    Function.Injective (stage18_localizedLaurentAlgHom k N M hM) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro f g
  constructor
  · intro h
    have hh := congrArg (stage18_localizedLaurentAlgHom k N M hM) h
    simpa only [stage18_localizedLaurent_algebraMap] using hh
  · intro h
    have he0 : stage18_boundedToArithmeticAlgHom k N f =
        stage18_boundedToArithmeticAlgHom k N g :=
      stage14_subfieldEntireLaurentAlgHom_injective k h
    have he : f = g := Subtype.ext
      (congrArg (fun a : subfieldEntireFunctionAlgebra k => a.val.val) he0)
    rw [he]

/-- Every realized fraction has its literal pointwise quotient formula. -/
theorem stage18_localizedPunctured_mk'
    (f : stage18_boundedArithmeticEntireAlgebra k N) (s : M)
    (z : Stage16PuncturedPlane) :
    stage18_localizedPuncturedAlgHom k N M hM
      (IsLocalization.mk' (Stage18BoundedArithmeticLocalization k N M) f s) z =
      f.val z.val / s.val.val z.val := by
  have h : stage18_localizedPuncturedAlgHom k N M hM
      (IsLocalization.mk' (Stage18BoundedArithmeticLocalization k N M) f s) =
      (fun z => f.val z.val / s.val.val z.val) := by
    apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
    funext z
    exact (mul_div_cancel₀ _ (hM s.property z)).symm
  exact congrFun h z

/-- The formal realization is the quotient of the same actual Taylor series. -/
theorem stage18_localizedLaurent_mk'
    (f : stage18_boundedArithmeticEntireAlgebra k N) (s : M) :
    stage18_localizedLaurentAlgHom k N M hM
      (IsLocalization.mk' (Stage18BoundedArithmeticLocalization k N M) f s) =
      stage18_boundedLaurentAlgHom k N f / stage18_boundedLaurentAlgHom k N s := by
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  exact (mul_div_cancel₀ _
    (stage16_laurent_denominator_isUnit k ⟨stage18_boundedToArithmeticAlgHom k N s, hM s.property⟩).ne_zero).symm

/-- Actual localization units cannot vanish at any nonzero complex point.
This follows from the ring map and its inverse unit, not an extra hypothesis. -/
theorem stage18_localized_unit_nonzero
    (u : (Stage18BoundedArithmeticLocalization k N M)ˣ) (z : Stage16PuncturedPlane) :
    stage18_localizedPuncturedAlgHom k N M hM (u : Stage18BoundedArithmeticLocalization k N M) z ≠ 0 := by
  exact (u.isUnit.map ((Pi.evalRingHom (fun _ : Stage16PuncturedPlane => ℂ) z).comp
    (stage18_localizedPuncturedAlgHom k N M hM).toRingHom)).ne_zero

include hM in
/-- The numerator in any representative of a unit is nonzero off the origin. -/
theorem stage18_localized_unit_numerator_nonzero
    (u : (Stage18BoundedArithmeticLocalization k N M)ˣ)
    (f : stage18_boundedArithmeticEntireAlgebra k N) (s : M)
    (hu : (u : Stage18BoundedArithmeticLocalization k N M) =
      IsLocalization.mk' (Stage18BoundedArithmeticLocalization k N M) f s) :
    ∀ z : ℂ, z ≠ 0 → f.val z ≠ 0 := by
  intro z hz hf
  have hn := stage18_localized_unit_nonzero k N M hM u ⟨z, hz⟩
  rw [hu, stage18_localizedPunctured_mk', hf, zero_div] at hn
  exact hn rfl

end Localization
end StrictEUnit
