import Stage19GeneratedArithmeticRealization
import Stage18LocalizedArithmeticUnitClassification

/-!
Unit classification for the actual Laurent/determinant-inverse coefficient
algebra, with its constructed genuine analytic and numerical realization.
All matrix entries are actual arithmetic entire functions of the specified
growth; only punctured determinant nonvanishing and positive growth degree
are assumed. This is not an assertion that every numerical E-unit lifts into
a matrix-generated ring, nor an existence theorem for an Andre frame.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- Use the existing coefficient semiring's monoid before specializing the matrix. -/
local instance (priority := 2000) stage19CoefficientMonoid
    {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (LaurentSeries k)) : Monoid (formalMatrixCoefficientAlgebra F) :=
  @MonoidWithZero.toMonoid _ (@Semiring.toMonoidWithZero _
    (formalMatrixCoefficientAlgebra F).toSemiring)

section Matrix
variable (k : Subfield ℂ) (N : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (stage18_boundedArithmeticEntireAlgebra k N))
    (hd : ∀ z : ℂ, z ≠ 0 → F.det.val z ≠ 0)

/-- Units in the actual generated coefficient algebra have an arithmetic
Laurent-monomial times exponential-polynomial form in the actual realization. -/
theorem stage19_generated_unit_eq_zpow_subfield_exp_polynomial
    (hN : 0 < N)
    (u : formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F))
    (hu : IsUnit u) :
    ∃ q : ℤ, ∃ c : k, ∃ P : Polynomial k,
      c ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      ∀ z : Stage16PuncturedPlane,
        stage19_generatedEvaluation k N F hd z u =
          (c : ℂ) * z.val^q * Complex.exp ((P.map k.subtype).eval z.val) := by
  obtain ⟨v, hv⟩ := hu.map (stage19_generatedToLocalization k N F hd)
  obtain ⟨q, c, P, hc, hP0, hPN, hP⟩ :=
    stage18_localized_unit_eq_zpow_subfield_exp_polynomial k N
      (stage18_boundedPuncturedDenominators k N) le_rfl hN v
  refine ⟨q, c, P, hc, hP0, hPN, fun z => ?_⟩
  change stage19_localizedAnalytic k N (stage19_generatedToLocalization k N F hd u) z = _
  rw [← hv]
  exact hP z

/-- The desired numerical scalar exponential follows for every genuine
coefficient-algebra unit, using the constructed value-at-one map. -/
theorem stage19_generated_unit_at_one_eq_subfield_scalar_exp
    (hN : 0 < N)
    (u : formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F))
    (hu : IsUnit u) :
    ∃ c a : k, c ≠ 0 ∧
      stage19_generatedEvaluation k N F hd ⟨1, one_ne_zero⟩ u =
        (c : ℂ) * Complex.exp (a : ℂ) := by
  obtain ⟨v, hv⟩ := hu.map (stage19_generatedToLocalization k N F hd)
  obtain ⟨c, a, hc, he⟩ := stage18_localized_unit_at_one_eq_subfield_scalar_exp k N
    (stage18_boundedPuncturedDenominators k N) le_rfl hN v
  refine ⟨c, a, hc, ?_⟩
  change stage19_localizedAnalytic k N (stage19_generatedToLocalization k N F hd u)
    ⟨1, one_ne_zero⟩ = _
  rw [← hv]
  exact he

attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower

/-- Combine proved logarithm removal with genuine analytic realization and
arithmetic unit classification. The formal PV candidate unit determines a
log-free coefficient unit, whose actual value at one has the claimed form. -/
theorem stage19_formalCandidate_unit_has_arithmetic_value
    (hN : 0 < N)
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((stage19_formalMatrix k N F).map RatFunc.C))
    (hu : IsUnit u) :
    ∃ s : formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F),
      IsUnit s ∧ RatFunc.C (s : LaurentSeries k) = (u : RatFunc (LaurentSeries k)) ∧
      ∃ c a : k, c ≠ 0 ∧
        stage19_generatedEvaluation k N F hd ⟨1, one_ne_zero⟩ s =
          (c : ℂ) * Complex.exp (a : ℂ) := by
  obtain ⟨s, hs, he⟩ := formalMatrix_unit_is_coefficient (stage19_formalMatrix k N F) u hu
  exact ⟨s, hs, he, stage19_generated_unit_at_one_eq_subfield_scalar_exp k N F hd hN s hs⟩


/-- The same constructed arithmetic value theorem survives an actual
invertible Laurent-logarithmic base change, by the proved equality of the
generated algebras rather than an extra invariance assumption. -/
theorem stage19_formalCandidate_base_change_unit_has_arithmetic_value
    (hN : 0 < N) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k)
      (((stage19_formalMatrix k N F).map RatFunc.C) *
        (Z : Matrix n n (LaurentLogBase k)).map
          (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))))
    (hu : IsUnit u) :
    ∃ s : formalMatrixCoefficientAlgebra (stage19_formalMatrix k N F),
      IsUnit s ∧ RatFunc.C (s : LaurentSeries k) = (u : RatFunc (LaurentSeries k)) ∧
      ∃ c a : k, c ≠ 0 ∧
        stage19_generatedEvaluation k N F hd ⟨1, one_ne_zero⟩ s =
          (c : ℂ) * Complex.exp (a : ℂ) := by
  obtain ⟨s, hs, he⟩ := formalMatrix_base_change_unit_is_coefficient
    (stage19_formalMatrix k N F) Z u hu
  exact ⟨s, hs, he, stage19_generated_unit_at_one_eq_subfield_scalar_exp k N F hd hN s hs⟩

end Matrix

/-- With the actual algebraic numbers as coefficient field, the realized
coefficient-unit value is a strict E-value unit by the proved arithmetic
construction of scalar exponential strict E-functions. -/
theorem stage19_generated_unit_at_one_isStrictEValueUnit
    (N : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (stage18_boundedArithmeticEntireAlgebra
      (algebraicClosure ℚ ℂ).toSubfield N))
    (hd : ∀ z : ℂ, z ≠ 0 → F.det.val z ≠ 0) (hN : 0 < N)
    (u : formalMatrixCoefficientAlgebra
      (stage19_formalMatrix (algebraicClosure ℚ ℂ).toSubfield N F))
    (hu : IsUnit u) :
    IsStrictEValueUnit
      (stage19_generatedEvaluation (algebraicClosure ℚ ℂ).toSubfield N F hd
        ⟨1, one_ne_zero⟩ u) := by
  obtain ⟨c, a, hc, he⟩ := stage19_generated_unit_at_one_eq_subfield_scalar_exp
    (algebraicClosure ℚ ℂ).toSubfield N F hd hN u hu
  rw [he]
  exact algebraic_scalar_exp_isStrictEValueUnit c a hc

end StrictEUnit
