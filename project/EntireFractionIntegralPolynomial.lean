import EntireLaurentMonicRelation
import EntireFractionMonicRationality

/-! New reconstruction, not recovered historical source.
Compose genuine Taylor transfer with analytic monic-root rigidity. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- An integral genuine entire-function Laurent quotient is polynomial.
The monic pointwise relation is proved from formal integrality, not assumed. -/
theorem entire_fraction_eq_polynomial_of_integral
    (F G : entireFunctionAlgebra) (hG : G ≠ 0)
    (hint : IsIntegral (Polynomial ℂ)
      (entireLaurentRingHom F / entireLaurentRingHom G)) :
    ∃ P : Polynomial ℂ,
      entireLaurentRingHom F / entireLaurentRingHom G =
        algebraMap (Polynomial ℂ) (LaurentSeries ℂ) P := by
  obtain ⟨p, hp, hroot⟩ := entire_fraction_exists_monic_relation F G hG hint
  have hG0 : G.val ≠ 0 := by
    intro h
    exact hG (Subtype.ext h)
  obtain ⟨P, hP⟩ := entire_fraction_polynomial_of_monic_relation
    F.property G.property hG0 hp hroot
  exact ⟨P, entire_fraction_eq_polynomial_of_cross_mul F G hG P hP⟩

end StrictEUnit
