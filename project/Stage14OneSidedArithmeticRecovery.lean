import Stage14OneSidedOriginGrowth
import EntireUnitArithmeticRecovery

/-! Arithmetic recovery from actual entire Taylor coefficients and one-sided
growth. No formal coefficient sequence is substituted for an analytic one. -/
noncomputable section
namespace StrictEUnit

/-- One-sided growth suffices for the actual subfield phase theorem. -/
theorem entire_unit_eq_subfield_exp_polynomial_of_one_sided_growth
    (k : Subfield ℂ) {w : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0)
    (hgrowth : HasPowerExponentialBound N w)
    (hcoeff : ∀ n, entireCauchyCoefficient w n ∈ k) :
    ∃ c : k, c ≠ 0 ∧ (c:ℂ) = w 0 ∧ ∃ Q : Polynomial k,
      Q.coeff 0 = 0 ∧ Q.natDegree ≤ N ∧
      ∀ z : ℂ, w z = (c:ℂ) * Complex.exp ((Q.map k.subtype).eval z) := by
  obtain ⟨P, hP0, hdegree, hphase, hp⟩ :=
    entire_unit_eq_exp_polynomial_of_one_sided_growth hN hw hnz hgrowth
  obtain ⟨Q, hQ⟩ := analytic_phase_over_subfield k hw hnz hcoeff P hP0 hp
  have hc : w 0 ∈ k := by simpa [entireCauchyCoefficient_zero hw] using hcoeff 0
  refine ⟨⟨w 0, hc⟩, ?_, rfl, Q, ?_, ?_, ?_⟩
  · intro he
    have := congrArg (fun x:k => (x:ℂ)) he
    exact hnz 0 this
  · apply k.subtype.injective
    simpa only [map_zero, ← Polynomial.coeff_map, hQ] using hP0
  · rw [← hQ, Polynomial.natDegree_map_eq_of_injective k.subtype.injective] at hdegree
    exact hdegree
  · simpa only [hQ] using hphase

/-- Multiplication by z^m shifts the actual Taylor coefficients by m. -/
theorem entireCauchyCoefficient_coordinate_pow_mul {w : ℂ → ℂ}
    (hw : Differentiable ℂ w) (m n : ℕ) :
    entireCauchyCoefficient (fun z => z^m * w z) (n+m) =
      entireCauchyCoefficient w n := by
  have ht : entireFormalTaylor (fun z : ℂ => z^m) = (PowerSeries.X : PowerSeries ℂ)^m := by
    simpa using entireFormalTaylor_polynomial ((Polynomial.X : Polynomial ℂ)^m)
  have hh := entireFormalTaylor_mul (differentiable_id.pow m) hw
  simp only [id_eq] at hh
  rw [ht] at hh
  have he := congrArg (PowerSeries.coeff ℂ (n+m)) hh
  simpa only [coeff_entireFormalTaylor, PowerSeries.coeff_X_pow_mul] using he

/-- The normalized entire factor inherits actual Taylor arithmetic by the
proved coefficient shift. This is not an assumption about formal generators. -/
theorem entire_eq_pow_subfield_exp_polynomial_of_one_sided_growth
    (k : Subfield ℂ) {v : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hv : Differentiable ℂ v)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound N v)
    (hcoeff : ∀ n, entireCauchyCoefficient v n ∈ k) :
    ∃ m : ℕ, ∃ c : k, ∃ Q : Polynomial k,
      (hv.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient v m ∧
      Q.coeff 0 = 0 ∧ Q.natDegree ≤ N ∧
      ∀ z, v z = (c : ℂ) * z^m * Complex.exp ((Q.map k.subtype).eval z) := by
  obtain ⟨m, w, hm, hw, hwnz, hvw, hgrowthw⟩ :=
    exists_entire_remove_origin_nat_with_one_sided_growth hv hnz hgrowth
  have hfun : v = fun z => z^m * w z := funext hvw
  have hcoeffw : ∀ n, entireCauchyCoefficient w n ∈ k := by
    intro n
    have hh := hcoeff (n+m)
    rw [hfun, entireCauchyCoefficient_coordinate_pow_mul hw m n] at hh
    exact hh
  obtain ⟨c, hc, hcw, Q, hQ0, hQN, hQ⟩ :=
    entire_unit_eq_subfield_exp_polynomial_of_one_sided_growth k hN hw hwnz hgrowthw hcoeffw
  refine ⟨m, c, Q, hm, hc, ?_, hQ0, hQN, fun z => ?_⟩
  · rw [hcw, hfun]
    simpa only [zero_add, entireCauchyCoefficient_zero hw] using
      (entireCauchyCoefficient_coordinate_pow_mul hw m 0).symm
  · rw [hvw z, hQ z]
    ring

/-- Determinant-shaped arithmetic normalization from the actual function's
own Taylor coefficients, not from an arithmetic formal surrogate. -/
theorem entire_eq_pow_subfield_exp_linear_of_one_sided_growth
    (k : Subfield ℂ) {v : ℂ → ℂ} (hv : Differentiable ℂ v)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound 1 v)
    (hcoeff : ∀ n, entireCauchyCoefficient v n ∈ k) :
    ∃ m : ℕ, ∃ c a : k,
      (hv.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient v m ∧
      ∀ z, v z = (c : ℂ) * z^m * Complex.exp ((a : ℂ)*z) := by
  obtain ⟨m, c, Q, hm, hc, hcoeffc, hQ0, hQN, hQ⟩ :=
    entire_eq_pow_subfield_exp_polynomial_of_one_sided_growth
      k (by decide) hv hnz hgrowth hcoeff
  refine ⟨m, c, Q.coeff 1, hm, hc, hcoeffc, fun z => ?_⟩
  rw [hQ z]
  have hp0 : (Q.map k.subtype).coeff 0 = 0 := by simp [hQ0]
  have hpN : (Q.map k.subtype).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective k.subtype.injective]
    exact hQN
  rw [eval_eq_coeff_one_mul_of_natDegree_le_one hp0 hpN]
  simp only [Polynomial.coeff_map, Subfield.coe_subtype]

end StrictEUnit
#print axioms StrictEUnit.entire_unit_eq_subfield_exp_polynomial_of_one_sided_growth
#print axioms StrictEUnit.entireCauchyCoefficient_coordinate_pow_mul

#print axioms StrictEUnit.entire_eq_pow_subfield_exp_polynomial_of_one_sided_growth
#print axioms StrictEUnit.entire_eq_pow_subfield_exp_linear_of_one_sided_growth
