import Stage28LaurentCompanion

/-! An explicit companion-frame input now supplies the Stage27 covering witness
by construction. Operator and actual arithmetic frame existence remain unproved. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

/-- An order-zero equation with nonzero monomial coefficient forces an entire
strict-E function to vanish. The argument includes the possibly singular origin. -/
theorem stage28_orderZero_eq_zero (k : Subfield ℂ) (r : ℕ) (c : k)
    (p : Fin 1 → Polynomial k) (f : ℂ → ℂ) (hf : IsStrictEFunction f)
    (h : Stage28MonomialLeadingODE k 0 r c p f) : f = (fun _ => 0) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast h.coefficient_ne_zero
  have heq : strictEFunctionTaylorRealization f hf = 0 := by
    apply stage17_arithmeticEntire_eq_of_units (algebraicClosure ℚ ℂ).toSubfield
    intro z
    change f (z : ℂ) = 0
    have he := stage28_scalarODE_last k 0 r c p f h (z : ℂ)
    simp only [Fin.sum_univ_zero, zero_add, iteratedDeriv_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hc (pow_ne_zero r z.ne_zero))
  exact congrArg (fun a : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield =>
    a.val.val) heq

/-- A nonzero strict-E solution of the displayed scalar operator has positive
order; this is proved rather than hidden in the existence input. -/
theorem stage28_order_pos_of_nonzero (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ) (hf : IsStrictEFunction f)
    (h : Stage28MonomialLeadingODE k m r c p f) (hne : f ≠ (fun _ => 0)) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst m
  exact hne (stage28_orderZero_eq_zero k r c p f hf h)

/-- With an actual arithmetic normal-form frame for this exact companion
matrix, the original function is covered. Neither derivative closure nor the
solution equation is an input. -/
def stage28_companionCover (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ) (hf : IsStrictEFunction f)
    (h : Stage28MonomialLeadingODE k m r c p f) (hm : 0 < m)
    (D : Stage27ArithmeticFrame k (Fin m))
    (hB : D.B = stage28_laurentCompanion k m r c p) : Stage27CoveredFunction k D f where
  v := stage28_derivativeJet m f
  strict := stage28_derivativeJet_strict hf m
  solution := by rw [hB]; exact stage28_derivativeJet_solution k m r c p f h
  component := ⟨0, hm⟩
  component_eq := stage28_derivativeJet_zero m hm f

/-- The precise remaining per-function input: choose an actual monomial-leading
annihilator together with an actual arithmetic frame for its constructed matrix.
This is NOT asserted for arbitrary annihilators. It is not proved here and is
not presented as the literal scalar statement of Andre's theorem. -/
def Stage28NonzeroOperatorFrameAvailability : Prop :=
  ∀ f : ℂ → ℂ, IsStrictEFunction f → f ≠ (fun _ => 0) →
    ∃ m r : ℕ, ∃ c : (algebraicClosure ℚ ℂ).toSubfield,
    ∃ p : Fin (m + 1) → Polynomial (algebraicClosure ℚ ℂ).toSubfield,
      Stage28MonomialLeadingODE (algebraicClosure ℚ ℂ).toSubfield m r c p f ∧
      ∃ D : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin m),
        D.B = stage28_laurentCompanion (algebraicClosure ℚ ℂ).toSubfield m r c p

/-- Stage28 removes the supplied solution-vector/component obligations from
Stage27's per-function input. The scalar operator/frame existence remains. -/
theorem stage28_nonzeroIndividualAvailability_of_operatorFrame
    (h : Stage28NonzeroOperatorFrameAvailability) :
    Stage27NonzeroIndividualArithmeticFrameAvailability := by
  intro f hf hne
  obtain ⟨m, r, c, p, hode, D, hB⟩ := h f hf hne
  exact ⟨m, D, ⟨stage28_companionCover _ m r c p f hf hode
    (stage28_order_pos_of_nonzero _ m r c p f hf hode hne) D hB⟩⟩

/-- Zero functions and simultaneous common-frame assembly are already proved
in Stage27, so no extra zero, direct-sum, or connection-coordinate input remains. -/
theorem stage28_commonAvailability_of_operatorFrame
    (h : Stage28NonzeroOperatorFrameAvailability) :
    StrictECommonArithmeticFrameAvailability :=
  stage27_commonAvailability_of_nonzero_individual
    (stage28_nonzeroIndividualAvailability_of_operatorFrame h)

/-- For a supplied actual companion frame, algebraic value coordinates are
consequences of Stage21, not new scalar-operator hypotheses. -/
theorem stage28_value_coverage_of_companionFrame
    (m r : ℕ) (c : (algebraicClosure ℚ ℂ).toSubfield)
    (p : Fin (m + 1) → Polynomial (algebraicClosure ℚ ℂ).toSubfield)
    (f : ℂ → ℂ) (hf : IsStrictEFunction f)
    (h : Stage28MonomialLeadingODE (algebraicClosure ℚ ℂ).toSubfield m r c p f)
    (hm : 0 < m)
    (D : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin m))
    (hB : D.B = stage28_laurentCompanion (algebraicClosure ℚ ℂ).toSubfield m r c p) :
    ∃ a : Fin m → (algebraicClosure ℚ ℂ).toSubfield,
      f 1 = ∑ j, (D.F ⟨0, hm⟩ j).val.val 1 * (a j : ℂ) := by
  obtain ⟨a, ha⟩ := stage21_strictESolutionVector_value_coverage D.B D.M D.F
    (stage28_derivativeJet m f) (stage28_derivativeJet_strict hf m) D.rational D.relation
    (by rw [hB]; exact stage28_derivativeJet_solution _ m r c p f h) D.invertible_at_one
  exact ⟨a, by simpa [stage28_derivativeJet] using ha ⟨0, hm⟩⟩

end StrictEUnit
