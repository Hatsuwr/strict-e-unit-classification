import Stage18BoundedArithmeticLocalization
import AlgebraicScalarExponential

/-! Arithmetic exponential-polynomial classification of actual units in the
localization of bounded arithmetic entire functions. The unit supplies its
numerator's nonvanishing, and the source carrier supplies both growth bounds.
The value-at-one endpoint is unconditional for these actual localization units.
It does not assert that an arbitrary numerical strict E-unit lifts here. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

section Localization
variable (k : Subfield ℂ) (N : ℕ)
    (M : Submonoid (stage18_boundedArithmeticEntireAlgebra k N))
    (hM : M ≤ stage18_boundedPuncturedDenominators k N)

/-- Every actual unit of the bounded arithmetic localization has the desired
arithmetic form in its actual punctured realization. No numerator zero-set or
reciprocal growth hypothesis remains at this endpoint. -/
theorem stage18_localized_unit_eq_zpow_subfield_exp_polynomial
    (hN : 0 < N) (u : (Stage18BoundedArithmeticLocalization k N M)ˣ) :
    ∃ q : ℤ, ∃ c : k, ∃ P : Polynomial k,
      c ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      ∀ z : Stage16PuncturedPlane,
        stage18_localizedPuncturedAlgHom k N M hM
          (u : Stage18BoundedArithmeticLocalization k N M) z =
          (c : ℂ) * z.val^q * Complex.exp ((P.map k.subtype).eval z.val) := by
  obtain ⟨f, s, hs⟩ := IsLocalization.mk'_surjective M
    (u : Stage18BoundedArithmeticLocalization k N M)
  obtain ⟨q, c, P, hc, hP0, hPN, hP⟩ :=
    stage18_entire_fraction_eq_zpow_subfield_exp_polynomial k hN
      f.property.1 s.val.property.1
      (stage18_localized_unit_numerator_nonzero k N M hM u f s hs.symm)
      (fun z hz => hM s.property ⟨z, hz⟩)
      f.property.2.2 s.val.property.2.2
      f.property.2.1 s.val.property.2.1
  refine ⟨q, c, P, hc, hP0, hPN, fun z => ?_⟩
  rw [← hs, stage18_localizedPunctured_mk']
  exact hP z.val z.property

/-- Actual evaluation at the ordinary point one has an arithmetic scalar and
an arithmetic exponential parameter, regardless of positive ramification N. -/
theorem stage18_localized_unit_at_one_eq_subfield_scalar_exp
    (hN : 0 < N) (u : (Stage18BoundedArithmeticLocalization k N M)ˣ) :
    ∃ c a : k, c ≠ 0 ∧
      stage18_localizedPuncturedAlgHom k N M hM
        (u : Stage18BoundedArithmeticLocalization k N M) ⟨1, one_ne_zero⟩ =
        (c : ℂ) * Complex.exp (a : ℂ) := by
  obtain ⟨q, c, P, hc, _, _, hP⟩ :=
    stage18_localized_unit_eq_zpow_subfield_exp_polynomial k N M hM hN u
  refine ⟨c, P.eval 1, hc, ?_⟩
  have he : (P.map k.subtype).eval 1 = (P.eval 1 : k) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_one k.subtype
  simpa only [one_zpow, mul_one, he] using hP ⟨1, one_ne_zero⟩

end Localization

/-- Specialization to the actual algebraic numbers inside the complex numbers.
This concludes an algebraic scalar exponential for this genuine ring's units,
not for numerical E-units lacking a lift into this ring. -/
theorem stage18_localized_unit_at_one_eq_algebraic_scalar_exp
    (N : ℕ) (M : Submonoid
      (stage18_boundedArithmeticEntireAlgebra (algebraicClosure ℚ ℂ).toSubfield N))
    (hM : M ≤ stage18_boundedPuncturedDenominators (algebraicClosure ℚ ℂ).toSubfield N)
    (hN : 0 < N)
    (u : (Stage18BoundedArithmeticLocalization (algebraicClosure ℚ ℂ).toSubfield N M)ˣ) :
    ∃ c a : AlgebraicComplex, c ≠ 0 ∧
      stage18_localizedPuncturedAlgHom (algebraicClosure ℚ ℂ).toSubfield N M hM
        (u : Stage18BoundedArithmeticLocalization (algebraicClosure ℚ ℂ).toSubfield N M)
        ⟨1, one_ne_zero⟩ = (c : ℂ) * Complex.exp (a : ℂ) :=
  stage18_localized_unit_at_one_eq_subfield_scalar_exp
    (algebraicClosure ℚ ℂ).toSubfield N M hM hN u

/-- The genuine unit's actual value is a strict E-value unit, using the proved
full arithmetic strict E-function construction of scalar exponentials. -/
theorem stage18_localized_unit_at_one_isStrictEValueUnit
    (N : ℕ) (M : Submonoid
      (stage18_boundedArithmeticEntireAlgebra (algebraicClosure ℚ ℂ).toSubfield N))
    (hM : M ≤ stage18_boundedPuncturedDenominators (algebraicClosure ℚ ℂ).toSubfield N)
    (hN : 0 < N)
    (u : (Stage18BoundedArithmeticLocalization (algebraicClosure ℚ ℂ).toSubfield N M)ˣ) :
    IsStrictEValueUnit
      (stage18_localizedPuncturedAlgHom (algebraicClosure ℚ ℂ).toSubfield N M hM
        (u : Stage18BoundedArithmeticLocalization (algebraicClosure ℚ ℂ).toSubfield N M)
        ⟨1, one_ne_zero⟩) := by
  obtain ⟨c, a, hc, he⟩ := stage18_localized_unit_at_one_eq_algebraic_scalar_exp N M hM hN u
  rw [he]
  exact algebraic_scalar_exp_isStrictEValueUnit c a hc

end StrictEUnit
