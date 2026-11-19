import AnalyticFormalTaylor
import EntireUnitExponentialPolynomial

/-! Arithmetic recovery for an actual entire unit. Membership of its actual
Taylor coefficients in k is an explicit input; it is not inferred from an
unconstructed arithmetic realization of the functional candidate. -/
noncomputable section
namespace StrictEUnit

/-- The actual analytic phase lies over the subfield when the actual entire
unit has its Taylor coefficients there. The formal ODE is derived, not assumed. -/
theorem analytic_phase_over_subfield (k : Subfield ℂ) {w : ℂ → ℂ}
    (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0)
    (hcoeff : ∀ n, entireCauchyCoefficient w n ∈ k)
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 0)
    (hp : ∀ z, HasDerivAt (fun t => P.eval t) (deriv w z / w z) z) :
    ∃ Q : Polynomial k, Q.map k.subtype = P := by
  apply phase_over_subfield_of_formal_equation k P hP0 (entireFormalTaylor w)
  · intro n
    simpa using hcoeff n
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [coeff_entireFormalTaylor, entireCauchyCoefficient_zero hw]
    exact hnz 0
  · exact entireFormalTaylor_phase_equation hw hnz P hp

/-- Entire unit classification with an actual subfield polynomial and nonzero
subfield leading scalar, from the actual Taylor-coefficient arithmetic input. -/
theorem entire_unit_eq_subfield_exp_polynomial (k : Subfield ℂ) {w : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0)
    (hgrowth : HasPowerExponentialBound N w)
    (hinv : HasPowerExponentialBound N (fun z => (w z)⁻¹))
    (hcoeff : ∀ n, entireCauchyCoefficient w n ∈ k) :
    ∃ c : k, c ≠ 0 ∧ (c:ℂ) = w 0 ∧ ∃ Q : Polynomial k,
      Q.coeff 0 = 0 ∧ Q.natDegree ≤ N ∧
      ∀ z : ℂ, w z = (c:ℂ) * Complex.exp ((Q.map k.subtype).eval z) := by
  obtain ⟨P,hP0,hdegree,hphase,hp⟩ := entire_unit_eq_exp_polynomial hN hw hnz hgrowth hinv
  obtain ⟨Q,hQ⟩ := analytic_phase_over_subfield k hw hnz hcoeff P hP0 hp
  have hc : w 0 ∈ k := by simpa [entireCauchyCoefficient_zero hw] using hcoeff 0
  refine ⟨⟨w 0,hc⟩, ?_, rfl, Q, ?_, ?_, ?_⟩
  · intro he
    have := congrArg (fun x:k => (x:ℂ)) he
    exact hnz 0 this
  · apply k.subtype.injective
    simpa only [map_zero, ← Polynomial.coeff_map, hQ] using hP0
  · rw [← hQ, Polynomial.natDegree_map_eq_of_injective k.subtype.injective] at hdegree
    exact hdegree
  · simpa only [hQ] using hphase
end StrictEUnit
#print axioms StrictEUnit.analytic_phase_over_subfield
#print axioms StrictEUnit.entire_unit_eq_subfield_exp_polynomial
