import Stage19GeneratedLaurentRange
import Stage18BoundedArithmeticLocalization
import ElementaryGeneratorGrowth

/-!
The actual matrix coefficient algebra embeds into a genuine localization of
bounded arithmetic entire functions. Every denominator is nonzero off zero.
The analytic realization is constructed by inverting the proved injective
Taylor map on its image, not by assigning values to arbitrary formal series.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- Use the full actual denominator monoid permitted off the origin. -/
abbrev Stage19ArithmeticLocalization (k : Subfield ℂ) (N : ℕ) :=
  Stage18BoundedArithmeticLocalization k N (stage18_boundedPuncturedDenominators k N)

/-- The genuine Taylor realization of this specified localization. -/
def stage19_localizedFormal (k : Subfield ℂ) (N : ℕ) :
    Stage19ArithmeticLocalization k N →ₐ[k] LaurentSeries k :=
  stage18_localizedLaurentAlgHom k N (stage18_boundedPuncturedDenominators k N) le_rfl

/-- The genuine punctured analytic realization of the same localization. -/
def stage19_localizedAnalytic (k : Subfield ℂ) (N : ℕ) :
    Stage19ArithmeticLocalization k N →ₐ[k] (Stage16PuncturedPlane → ℂ) :=
  stage18_localizedPuncturedAlgHom k N (stage18_boundedPuncturedDenominators k N) le_rfl

/-- The coordinate has the required growth for every degree parameter. -/
def stage19_boundedCoordinate (k : Subfield ℂ) (N : ℕ) :
    stage18_boundedArithmeticEntireAlgebra k N :=
  stage18_boundArithmeticFunction k N (subfieldEntireCoordinate k)
    (powerExponentialBound_coordinate N id)

/-- The actual coordinate is among the permissible bounded denominators. -/
theorem stage19_boundedCoordinate_mem_denominators (k : Subfield ℂ) (N : ℕ) :
    stage19_boundedCoordinate k N ∈ stage18_boundedPuncturedDenominators k N := by
  intro z
  exact z.property

/-- The bounded coordinate really has the fixed formal Laurent expansion. -/
theorem stage19_boundedCoordinate_formal (k : Subfield ℂ) (N : ℕ) :
    stage18_boundedLaurentAlgHom k N (stage19_boundedCoordinate k N) =
      laurentPolynomialToSeries (LaurentPolynomial.T 1) := by
  change stage14_subfieldEntireLaurentAlgHom k (subfieldEntireCoordinate k) = _
  rw [stage14_subfieldEntireLaurentAlgHom_apply, subfieldEntireTaylorAlgHom_coordinate,
    HahnSeries.ofPowerSeries_X]
  exact (laurentPolynomialToSeries_single 1 1).symm

/-- The coordinate and its inverse are both in the actual localization's
formal image. Their source is the actual coordinate, not a formal placeholder. -/
theorem stage19_coordinate_and_inverse_mem_formal_range (k : Subfield ℂ) (N : ℕ) :
    laurentPolynomialToSeries (LaurentPolynomial.T 1) ∈ (stage19_localizedFormal k N).range ∧
    laurentPolynomialToSeries (LaurentPolynomial.T (-1)) ∈ (stage19_localizedFormal k N).range := by
  let t : stage18_boundedArithmeticEntireAlgebra k N := stage19_boundedCoordinate k N
  let r := algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
    (Stage19ArithmeticLocalization k N) t
  have hr : stage19_localizedFormal k N r =
      laurentPolynomialToSeries (LaurentPolynomial.T 1) := by
    rw [stage19_localizedFormal, stage18_localizedLaurent_algebraMap]
    exact stage19_boundedCoordinate_formal k N
  have hu : IsUnit r := IsLocalization.map_units _
    (⟨t, stage19_boundedCoordinate_mem_denominators k N⟩ :
      stage18_boundedPuncturedDenominators k N)
  refine ⟨⟨r, hr⟩, ?_⟩
  have hi := stage19_inverse_mem_range_of_isUnit (stage19_localizedFormal k N) r hu
  rw [hr] at hi
  have hprod : laurentPolynomialToSeries (LaurentPolynomial.T 1 : LaurentPolynomial k) *
      laurentPolynomialToSeries (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  rw [eq_inv_of_mul_eq_one_right hprod]
  exact hi

section Matrix
variable (k : Subfield ℂ) (N : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (stage18_boundedArithmeticEntireAlgebra k N))
    (hd : ∀ z : ℂ, z ≠ 0 → F.det.val z ≠ 0)

/-- The matrix consists of the actual Taylor expansions of the supplied entries. -/
def stage19_formalMatrix : Matrix n n (LaurentSeries k) :=
  F.map (stage18_boundedLaurentAlgHom k N)

/-- Actual entries and a determinant nonzero off zero imply membership of every
generator, and hence of the whole actual coefficient algebra, in the genuine
localization image. No desired realization or unit classification is assumed. -/
theorem stage19_generated_algebra_le_formal_range
    (hd : ∀ z : ℂ, z ≠ 0 → F.det.val z ≠ 0) :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) ≤
      (stage19_localizedFormal k N).range := by
  obtain ⟨ht, hti⟩ := stage19_coordinate_and_inverse_mem_formal_range k N
  apply stage19_formalMatrixCoefficientAlgebra_le _ _ ht hti
  · have hu : IsUnit (algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage19ArithmeticLocalization k N) F.det) :=
      IsLocalization.map_units _ (⟨F.det, fun z => hd z.val z.property⟩ :
        stage18_boundedPuncturedDenominators k N)
    have hi := stage19_inverse_mem_range_of_isUnit (stage19_localizedFormal k N)
      (algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage19ArithmeticLocalization k N) F.det) hu
    rw [stage19_localizedFormal, stage18_localizedLaurent_algebraMap] at hi
    change ((stage18_boundedLaurentAlgHom k N).toRingHom F.det)⁻¹ ∈
      (stage19_localizedFormal k N).range at hi
    rw [RingHom.map_det] at hi
    exact hi
  · intro i j
    refine ⟨algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
      (Stage19ArithmeticLocalization k N) (F i j), ?_⟩
    exact stage18_localizedLaurent_algebraMap k N _ le_rfl (F i j)

/-- Canonical localization preimage of an actual generated coefficient element.
The inverse is justified by the proved injectivity of genuine Taylor expansion. -/
def stage19_generatedToLocalization :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) →ₐ[k]
      Stage19ArithmeticLocalization k N :=
  (AlgEquiv.ofInjective (stage19_localizedFormal k N)
    (stage18_localizedLaurentAlgHom_injective k N _ le_rfl)).symm.toAlgHom.comp
      (Subalgebra.inclusion (stage19_generated_algebra_le_formal_range k N F hd))

/-- The constructed inverse returns precisely the original formal element. -/
theorem stage19_generatedToLocalization_formal
    (u : formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F)) :
    stage19_localizedFormal k N (stage19_generatedToLocalization k N F hd u) =
      (u : LaurentSeries k) := by
  let e := AlgEquiv.ofInjective (stage19_localizedFormal k N)
    (stage18_localizedLaurentAlgHom_injective k N _ le_rfl)
  exact congrArg Subtype.val (e.apply_symm_apply
    (Subalgebra.inclusion (stage19_generated_algebra_le_formal_range k N F hd) u))

/-- The actual coefficient ring has a faithful punctured-function realization. -/
def stage19_generatedAnalytic :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) →ₐ[k]
      (Stage16PuncturedPlane → ℂ) :=
  (stage19_localizedAnalytic k N).comp (stage19_generatedToLocalization k N F hd)

/-- The constructed analytic realization is injective. -/
theorem stage19_generatedAnalytic_injective :
    Function.Injective (stage19_generatedAnalytic k N F hd) := by
  intro u v h
  have hq := stage18_localizedPuncturedAlgHom_injective k N _ le_rfl h
  apply Subtype.ext
  calc
    (u : LaurentSeries k) = stage19_localizedFormal k N
        (stage19_generatedToLocalization k N F hd u) :=
      (stage19_generatedToLocalization_formal k N F hd u).symm
    _ = stage19_localizedFormal k N (stage19_generatedToLocalization k N F hd v) :=
      congrArg (stage19_localizedFormal k N) hq
    _ = (v : LaurentSeries k) := stage19_generatedToLocalization_formal k N F hd v

/-- Evaluation at a genuine nonzero complex point is an actual algebra map. -/
def stage19_generatedEvaluation (z : Stage16PuncturedPlane) :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) →ₐ[k] ℂ where
  toFun u := stage19_generatedAnalytic k N F hd u z
  map_zero' := congrFun (map_zero (stage19_generatedAnalytic k N F hd)) z
  map_one' := congrFun (map_one (stage19_generatedAnalytic k N F hd)) z
  map_add' u v := congrFun ((stage19_generatedAnalytic k N F hd).map_add' u v) z
  map_mul' u v := congrFun (map_mul (stage19_generatedAnalytic k N F hd) u v) z
  commutes' a := congrFun ((stage19_generatedAnalytic k N F hd).commutes a) z

/-- Compatibility for every actual localization preimage, with no arbitrary
choice of values for Laurent series. -/
theorem stage19_generatedToLocalization_of_preimage
    (q : Stage19ArithmeticLocalization k N)
    (hq : stage19_localizedFormal k N q ∈
      formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F)) :
    stage19_generatedToLocalization k N F hd ⟨stage19_localizedFormal k N q, hq⟩ = q := by
  apply stage18_localizedLaurentAlgHom_injective k N _ le_rfl
  exact stage19_generatedToLocalization_formal k N F hd _

/-- Exact compatibility of constructed numerical evaluation with the actual
analytic evaluation of every source representative. -/
theorem stage19_generatedEvaluation_of_preimage
    (q : Stage19ArithmeticLocalization k N)
    (hq : stage19_localizedFormal k N q ∈
      formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F))
    (z : Stage16PuncturedPlane) :
    stage19_generatedEvaluation k N F hd z ⟨stage19_localizedFormal k N q, hq⟩ =
      stage19_localizedAnalytic k N q z := by
  change stage19_localizedAnalytic k N
    (stage19_generatedToLocalization k N F hd ⟨_, hq⟩) z = _
  rw [stage19_generatedToLocalization_of_preimage]


/-- An actual matrix entry as an element of the generated coefficient algebra. -/
def stage19_generatedEntry (i j : n) :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) :=
  ⟨stage19_formalMatrix k N F i j,
    Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩))⟩

/-- The canonical localization preimage of a generator is the original entire
entry, inserted by the actual localization algebra map. -/
theorem stage19_generatedToLocalization_entry (i j : n) :
    stage19_generatedToLocalization k N F hd (stage19_generatedEntry k N F i j) =
      algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage19ArithmeticLocalization k N) (F i j) := by
  apply stage18_localizedLaurentAlgHom_injective k N _ le_rfl
  exact (stage19_generatedToLocalization_formal k N F hd
    (stage19_generatedEntry k N F i j)).trans
      (stage18_localizedLaurent_algebraMap k N _ le_rfl (F i j)).symm

/-- The numerical realization agrees exactly with each supplied actual entry. -/
theorem stage19_generatedEvaluation_entry (i j : n) (z : Stage16PuncturedPlane) :
    stage19_generatedEvaluation k N F hd z (stage19_generatedEntry k N F i j) =
      (F i j).val z.val := by
  change stage19_localizedAnalytic k N
    (stage19_generatedToLocalization k N F hd (stage19_generatedEntry k N F i j)) z = _
  rw [stage19_generatedToLocalization_entry]
  exact congrFun (stage18_localizedPunctured_algebraMap k N _ le_rfl (F i j)) z



/-- The fixed formal Laurent polynomial included as an actual generator. -/
def stage19_generatedLaurentPolynomial (p : LaurentPolynomial k) :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) :=
  ⟨laurentPolynomialToSeries p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩

/-- Evaluation sends the actual formal coordinate to the specified analytic
coordinate. This identifies the base variable, rather than just the entries. -/
theorem stage19_generatedEvaluation_coordinate (z : Stage16PuncturedPlane) :
    stage19_generatedEvaluation k N F hd z
      (stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T 1)) = z.val := by
  have he : stage19_generatedToLocalization k N F hd
      (stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T 1)) =
      algebraMap (stage18_boundedArithmeticEntireAlgebra k N)
        (Stage19ArithmeticLocalization k N) (stage19_boundedCoordinate k N) := by
    apply stage18_localizedLaurentAlgHom_injective k N _ le_rfl
    exact (stage19_generatedToLocalization_formal k N F hd
      (stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T 1))).trans
        ((stage19_boundedCoordinate_formal k N).symm.trans
          (stage18_localizedLaurent_algebraMap k N _ le_rfl
            (stage19_boundedCoordinate k N)).symm)
  change stage19_localizedAnalytic k N
    (stage19_generatedToLocalization k N F hd
      (stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T 1))) z = _
  rw [he]
  exact congrFun (stage18_localizedPunctured_algebraMap k N _ le_rfl
    (stage19_boundedCoordinate k N)) z

/-- The inverse coordinate generator evaluates to the actual reciprocal on
the punctured plane, as forced by the proved multiplicative identity. -/
theorem stage19_generatedEvaluation_coordinate_inverse (z : Stage16PuncturedPlane) :
    stage19_generatedEvaluation k N F hd z
      (stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T (-1))) = z.val⁻¹ := by
  have hp : stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T 1) *
      stage19_generatedLaurentPolynomial k N F (LaurentPolynomial.T (-1)) = 1 := by
    apply Subtype.ext
    change laurentPolynomialToSeries (LaurentPolynomial.T 1 : LaurentPolynomial k) *
      laurentPolynomialToSeries (LaurentPolynomial.T (-1)) = 1
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  have he := congrArg (stage19_generatedEvaluation k N F hd z) hp
  rw [map_mul, map_one, stage19_generatedEvaluation_coordinate] at he
  exact eq_inv_of_mul_eq_one_right he

/-- The actual determinant-inverse generator in the coefficient algebra. -/
def stage19_generatedDeterminantInverse :
    formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F) :=
  ⟨(stage19_formalMatrix k N F).det⁻¹,
    Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))⟩

/-- The determinant-inverse generator has the genuine fraction 1/det F as its
localization preimage. Punctured nonvanishing validates this denominator. -/
theorem stage19_generatedToLocalization_determinantInverse :
    stage19_generatedToLocalization k N F hd (stage19_generatedDeterminantInverse k N F) =
      IsLocalization.mk' (Stage19ArithmeticLocalization k N) 1
        (⟨F.det, fun z => hd z.val z.property⟩ : stage18_boundedPuncturedDenominators k N) := by
  apply stage18_localizedLaurentAlgHom_injective k N _ le_rfl
  change stage19_localizedFormal k N
    (stage19_generatedToLocalization k N F hd (stage19_generatedDeterminantInverse k N F)) = _
  rw [stage19_generatedToLocalization_formal, stage18_localizedLaurent_mk']
  change (stage19_formalMatrix k N F).det⁻¹ =
    stage18_boundedLaurentAlgHom k N 1 / stage18_boundedLaurentAlgHom k N F.det
  rw [map_one, one_div]
  congr 1
  exact ((stage18_boundedLaurentAlgHom k N).toRingHom.map_det F).symm

/-- The constructed numerical map gives the literal reciprocal of the actual
determinant at every nonzero complex point, with no totalization at a zero. -/
theorem stage19_generatedEvaluation_determinantInverse (z : Stage16PuncturedPlane) :
    stage19_generatedEvaluation k N F hd z (stage19_generatedDeterminantInverse k N F) =
      (F.det.val z.val)⁻¹ := by
  change stage19_localizedAnalytic k N
    (stage19_generatedToLocalization k N F hd (stage19_generatedDeterminantInverse k N F)) z = _
  rw [stage19_generatedToLocalization_determinantInverse]
  exact (stage18_localizedPunctured_mk' k N _ le_rfl 1
    (⟨F.det, fun z => hd z.val z.property⟩ : stage18_boundedPuncturedDenominators k N) z).trans
      (one_div _)

/-- Every realized coefficient has an actual analytic representative off zero. -/
theorem stage19_generatedAnalytic_has_analytic_representative
    (u : formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g {z : ℂ | z ≠ 0} ∧
      ∀ z : Stage16PuncturedPlane, stage19_generatedAnalytic k N F hd u z = g z.val := by
  obtain ⟨f, s, hs⟩ := IsLocalization.mk'_surjective
    (stage18_boundedPuncturedDenominators k N)
    (stage19_generatedToLocalization k N F hd u)
  refine ⟨fun z => f.val z / s.val.val z, ?_, ?_⟩
  · intro z hz
    exact (f.property.1.analyticAt z).fun_div
      (s.val.property.1.analyticAt z) (s.property ⟨z, hz⟩)
  · intro z
    change stage19_localizedAnalytic k N (stage19_generatedToLocalization k N F hd u) z = _
    rw [← hs]
    exact stage18_localizedPunctured_mk' k N _ le_rfl f s z

end Matrix
end StrictEUnit
