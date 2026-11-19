import Stage21ActualSolutionValues

/-! Vector and strict-E specializations of actual arithmetic value coverage. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- Every actual arithmetic solution vector of z v′=Bv has value at one in the
k-span of the columns of the actual frame F(1), with no supplied connection
coordinates. This includes the empty-dimensional case. -/
theorem stage21_actualSolutionVector_value_coverage [IsAlgClosed k]
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (v : n → subfieldEntireFunctionAlgebra k)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a)
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (hv : ∀ z : ℂˣ, ∀ i, (z : ℂ) * deriv (v i).val.val (z : ℂ) =
      ∑ l, LaurentPolynomial.eval₂ k.subtype z (B i l) * (v l).val.val (z : ℂ))
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ∃ c : n → k, ∀ i, (v i).val.val 1 = ∑ l, (F i l).val.val 1 * (c l : ℂ) := by
  classical
  by_cases hn : Nonempty n
  · let j : n := Classical.choice hn
    let V : Matrix n n (subfieldEntireFunctionAlgebra k) := fun i _ => v i
    have hV : Stage17ActualEulerFrameRelation k B 0 V := by
      intro z i j
      change (z : ℂ) * deriv (v i).val.val (z : ℂ) =
        (∑ l, LaurentPolynomial.eval₂ k.subtype z (B i l) * (v l).val.val (z : ℂ)) -
          ∑ l, (v i).val.val (z : ℂ) * (0 : ℂ)
      simpa only [mul_zero, Finset.sum_const_zero, sub_zero] using hv z i
    obtain ⟨C, hC⟩ := stage21_actualSolutionMatrix_value_coverage k B M F V hrat hF hV h1
    refine ⟨fun l => C l j, fun i => ?_⟩
    exact congrArg (fun Q : Matrix n n ℂ => Q i j) hC
  · letI : IsEmpty n := not_nonempty_iff.mp hn
    exact ⟨fun _ => 0, fun i => isEmptyElim i⟩

/-- Strict-E solutions supply the arithmetic entire inputs, and the exact
algebraic-number coefficient field supplies its proved algebraic closedness.
The actual arithmetic frame and both actual systems remain explicit. -/
theorem stage21_strictESolutionVector_value_coverage
    (B : Matrix n n (LaurentPolynomial (algebraicClosure ℚ ℂ).toSubfield))
    (M : Matrix n n (algebraicClosure ℚ ℂ).toSubfield)
    (F : Matrix n n (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield))
    (v : n → ℂ → ℂ) (he : ∀ i, IsStrictEFunction (v i))
    (hrat : ∀ a : (algebraicClosure ℚ ℂ).toSubfield,
      (minpoly (algebraicClosure ℚ ℂ).toSubfield M).IsRoot a →
      ∃ q : ℚ, (q : (algebraicClosure ℚ ℂ).toSubfield) = a)
    (hF : Stage17ActualEulerFrameRelation (algebraicClosure ℚ ℂ).toSubfield B M F)
    (hv : ∀ z : ℂˣ, ∀ i, (z : ℂ) * deriv (v i) (z : ℂ) =
      ∑ l, LaurentPolynomial.eval₂ (algebraicClosure ℚ ℂ).toSubfield.subtype z (B i l) *
        v l (z : ℂ))
    (h1 : (F.map (stage14_subfieldEntireEvaluation (algebraicClosure ℚ ℂ).toSubfield 1)).det ≠ 0) :
    ∃ c : n → (algebraicClosure ℚ ℂ).toSubfield,
      ∀ i, v i 1 = ∑ l, (F i l).val.val 1 * (c l : ℂ) := by
  letI : IsAlgClosed (algebraicClosure ℚ ℂ).toSubfield :=
    stage17_algebraicTaylorField_isAlgClosed
  exact stage21_actualSolutionVector_value_coverage (algebraicClosure ℚ ℂ).toSubfield
    B M F (fun i => strictEFunctionTaylorRealization (v i) (he i)) hrat hF hv h1

end StrictEUnit
