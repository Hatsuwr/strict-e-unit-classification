import Stage33ScalarBasisNondegeneracy
import Stage33FormalCompanion
import Stage29InitialNondegeneracy
import Stage28CompanionFrameCoverage

/-! A scalar normal-form basis yields the actual strict-E arithmetic frame
for the exact original ordinary-jet companion. Scalar existence is explicit. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
variable (k : Subfield ℂ) (m r : ℕ) (c : k)
  (p : Fin (m + 1) → Polynomial k) (hc : c ≠ 0)
  (hp : p (Fin.last m) = Polynomial.monomial r c)

include hc hp

/-- Differentiating the literal jet factorization and cancelling its genuine
right unit derives the formal frame equation with the original companion. -/
theorem stage33_scalarNormalForm_formalFrame_ode (S : Stage33ScalarNormalForm k m p) :
    matrixDerivative (formalAmbientDerivation S.N S.ramification_ne_zero)
      (stage17_formalFrame k S.N S.ramification_ne_zero (stage33_entireJetFrame k m S.e S.M)) =
      (stage28_laurentCompanion k m r c p).map (stage17_laurentAmbientPullback k S.N) *
        stage17_formalFrame k S.N S.ramification_ne_zero (stage33_entireJetFrame k m S.e S.M) -
      stage17_formalFrame k S.N S.ramification_ne_zero (stage33_entireJetFrame k m S.e S.M) *
        (stage33_shiftedResidue k S.M (m - 1)).map (algebraMap k (RatFunc (LaurentSeries k))) := by
  apply stage33_frame_ode_of_factorization _ _ _ _
    (stage33_shiftedFormalBaseUnit k S.N S.ramification_ne_zero (m - 1) S.Z)
  · rw [← stage33_scalarNormalFormJet_factorization k S.N S.ramification_ne_zero
      m S.e S.M S.Z S.base_equation]
    exact stage33_formal_scalarJet_ode k S.N S.ramification_ne_zero m r c p hc hp
      (stage33_scalarNormalFormRow k S.N S.ramification_ne_zero S.e S.Z) S.scalar_equation
  · exact stage33_shiftedFormalBaseUnit_ode k S.N S.ramification_ne_zero (m - 1)
      S.M S.Z S.base_equation

/-- Genuine ramified Taylor injectivity transports the proved formal equation
back to the actual punctured analytic frame equation. -/
theorem stage33_scalarNormalForm_actualFrame_relation (S : Stage33ScalarNormalForm k m p) :
    Stage17ActualEulerFrameRelation k (stage28_laurentCompanion k m r c p)
      (stage33_shiftedResidue k S.M (m - 1)) (stage33_entireJetFrame k m S.e S.M) :=
  stage32_actualEulerFrame_of_formalFrame_ode k S.N S.ramification_ne_zero _ _ _
    (stage33_scalarNormalForm_formalFrame_ode k m r c p hc hp S)

/-- Nonzero determinant at one is a conclusion of scalar independence,
factorization, and the actual frame equation; it is not a normal-form input. -/
theorem stage33_scalarNormalForm_det_at_one (hm : 0 < m) (S : Stage33ScalarNormalForm k m p) :
    ((stage33_entireJetFrame k m S.e S.M).map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 := by
  apply (stage29_arithmeticFrame_formal_det_ne_zero_iff_at_one k S.N S.ramification_ne_zero
    (stage28_laurentCompanion k m r c p) (stage33_shiftedResidue k S.M (m - 1))
    (stage33_entireJetFrame k m S.e S.M)
    (stage33_scalarNormalForm_actualFrame_relation k m r c p hc hp S)).mp
  exact stage33_entireJetFrame_formal_det_ne_zero k m p hm S
    (stage33_formal_leading_ne_zero k S.N S.ramification_ne_zero m r c p hc hp)

omit hc hp

/-- The actual arithmetic frame is constructed over the exact algebraic-number
subfield. Its companion remains the original Stage28 matrix, without changing f. -/
def stage33_arithmeticFrame_of_scalarNormalForm
    (m r : ℕ) (c : (algebraicClosure ℚ ℂ).toSubfield)
    (p : Fin (m + 1) → Polynomial (algebraicClosure ℚ ℂ).toSubfield)
    (hc : c ≠ 0) (hp : p (Fin.last m) = Polynomial.monomial r c) (hm : 0 < m)
    (S : Stage33ScalarNormalForm (algebraicClosure ℚ ℂ).toSubfield m p) :
    Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin m) where
  B := stage28_laurentCompanion _ m r c p
  M := stage33_shiftedResidue _ S.M (m - 1)
  F := stage33_entireJetFrame _ m S.e S.M
  strict := stage33_entireJetFrame_strict m S.e S.M S.strict
  rational := stage33_shiftedResidue_rational _ S.M (m - 1) S.rational
  relation := stage33_scalarNormalForm_actualFrame_relation _ m r c p hc hp S
  invertible_at_one := stage33_scalarNormalForm_det_at_one _ m r c p hc hp hm S

/-- The remaining arithmetic existence premise concerns only a chosen scalar
operator and scalar normal form. It does not supply the target frame. -/
def Stage33NonzeroScalarNormalFormAvailability : Prop :=
  ∀ f : ℂ → ℂ, IsStrictEFunction f → f ≠ (fun _ => 0) →
    ∃ m r : ℕ, ∃ c : (algebraicClosure ℚ ℂ).toSubfield,
    ∃ p : Fin (m + 1) → Polynomial (algebraicClosure ℚ ℂ).toSubfield,
      Stage28MonomialLeadingODE (algebraicClosure ℚ ℂ).toSubfield m r c p f ∧
      Nonempty (Stage33ScalarNormalForm (algebraicClosure ℚ ℂ).toSubfield m p)

/-- Scalar availability implies the previously required exact companion-frame
availability by the proved construction, with the original f untouched. -/
theorem stage33_operatorFrameAvailability_of_scalarNormalForm
    (h : Stage33NonzeroScalarNormalFormAvailability) : Stage28NonzeroOperatorFrameAvailability := by
  intro f hf hne
  obtain ⟨m, r, c, p, hode, ⟨S⟩⟩ := h f hf hne
  have hm := stage28_order_pos_of_nonzero _ m r c p f hf hode hne
  exact ⟨m, r, c, p, hode,
    stage33_arithmeticFrame_of_scalarNormalForm m r c p hode.coefficient_ne_zero hode.leading hm S,
    rfl⟩

/-- Common frame availability follows from scalar normal-form availability;
the latter deep arithmetic existence theorem is not asserted here. -/
theorem stage33_commonFrameAvailability_of_scalarNormalForm
    (h : Stage33NonzeroScalarNormalFormAvailability) : StrictECommonArithmeticFrameAvailability :=
  stage28_commonAvailability_of_operatorFrame (stage33_operatorFrameAvailability_of_scalarNormalForm h)

end StrictEUnit
