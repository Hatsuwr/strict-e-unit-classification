import Stage33ScalarNormalFormData
import Stage33ShiftedFormalUnit

/-! The remaining deep input is a scalar normal-form basis for a chosen
operator. The defined scalar row satisfies the operator and is independent
over the exact constant field. Its frame's nondegeneracy is then proved. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit

/- Explicit scalar-basis data, without a frame equation, frame determinant,
initial inverse, or assertion of existence. The scalar row is literally e·Z. -/

variable (k : Subfield ℂ) (m : ℕ) (p : Fin (m + 1) → Polynomial k)

/-- Scalar independence and the scalar equation imply the ordinary jet
matrix determinant is nonzero. This invokes the proved same-system theorem. -/
theorem stage33_scalarNormalFormJet_det_ne_zero (hm : 0 < m)
    (S : Stage33ScalarNormalForm k m p)
    (ha : Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k S.N S.ramification_ne_zero (subfieldEntireCoordinate k))
      (p (Fin.last m)) ≠ 0) :
    (stage33_scalarNormalFormJet k S.N S.ramification_ne_zero m S.e S.Z).det ≠ 0 := by
  exact stage30_scaled_formal_jet_det_ne_zero S.N S.ramification_ne_zero
    (stage17_ramifiedEntireFormalAlgHom k S.N S.ramification_ne_zero
      (subfieldEntireCoordinate k))⁻¹
    (inv_ne_zero (stage17_ramifiedEntireFormal_coordinate_ne_zero k S.N S.ramification_ne_zero))
    m hm (fun l => Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k S.N S.ramification_ne_zero
        (subfieldEntireCoordinate k)) (p l)) ha
    (stage33_scalarNormalFormRow k S.N S.ramification_ne_zero S.e S.Z)
    S.scalar_equation S.independent

/-- The actual pole-cleared frame has nonzero genuine formal determinant,
derived through literal jet factorization, not assumed at a chosen point. -/
theorem stage33_entireJetFrame_formal_det_ne_zero (hm : 0 < m)
    (S : Stage33ScalarNormalForm k m p)
    (ha : Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k S.N S.ramification_ne_zero (subfieldEntireCoordinate k))
      (p (Fin.last m)) ≠ 0) :
    (stage17_formalFrame k S.N S.ramification_ne_zero
      (stage33_entireJetFrame k m S.e S.M)).det ≠ 0 := by
  have hj := stage33_scalarNormalFormJet_det_ne_zero k m p hm S ha
  rw [stage33_scalarNormalFormJet_factorization k S.N S.ramification_ne_zero
    m S.e S.M S.Z S.base_equation, Matrix.det_mul] at hj
  exact fun h => hj (by rw [h, zero_mul])

end StrictEUnit
