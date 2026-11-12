import Stage21ActualSolutionVectors
import StrictEAlgebraicRescaling

/-! A precise, explicitly unproved common arithmetic-frame availability input,
and its checked value-algebra consequence. This is not a formalization of
Andre's normal-form theorem or of the companion/direct-sum constructions. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The algebraic span conclusion of actual solution coverage gives literal
membership in the finite frame-value algebra. -/
theorem value_mem_frameAlgebra_of_coordinates
    (k : Subfield ℂ) {n : Type*} [Fintype n]
    (F : Matrix n n ℂ) (c : n → k) (i : n) (x : ℂ)
    (hx : x = ∑ l, F i l * (c l : ℂ)) :
    x ∈ Algebra.adjoin k (Set.range fun ij : n × n => F ij.1 ij.2) := by
  rw [hx]
  apply Subalgebra.sum_mem
  intro j hj
  apply Subalgebra.mul_mem
  · exact Algebra.subset_adjoin ⟨(i,j), rfl⟩
  · exact (Algebra.adjoin k _).algebraMap_mem (c j)

/-- Exact common-frame availability needed from the still-unformalized
arithmetic normal-form/companion/direct-sum input. It concerns actual functions
and their actual systems, not any conclusion about numerical units. -/
def StrictECommonArithmeticFrameAvailability : Prop :=
  ∀ f g : ℂ → ℂ, IsStrictEFunction f → IsStrictEFunction g →
    ∃ d : ℕ,
    ∃ B : Matrix (Fin d) (Fin d) (LaurentPolynomial (algebraicClosure ℚ ℂ).toSubfield),
    ∃ M : Matrix (Fin d) (Fin d) (algebraicClosure ℚ ℂ).toSubfield,
    ∃ F : Matrix (Fin d) (Fin d)
      (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield),
      (∀ i j, IsStrictEFunction (F i j).val.val) ∧
      (∀ a : (algebraicClosure ℚ ℂ).toSubfield,
        (minpoly (algebraicClosure ℚ ℂ).toSubfield M).IsRoot a →
          ∃ q : ℚ, (q : (algebraicClosure ℚ ℂ).toSubfield) = a) ∧
      Stage17ActualEulerFrameRelation (algebraicClosure ℚ ℂ).toSubfield B M F ∧
      (F.map (stage14_subfieldEntireEvaluation (algebraicClosure ℚ ℂ).toSubfield 1)).det ≠ 0 ∧
      ∃ v w : Fin d → ℂ → ℂ,
        (∀ i, IsStrictEFunction (v i)) ∧ (∀ i, IsStrictEFunction (w i)) ∧
        (∀ z : ℂˣ, ∀ i, (z : ℂ) * deriv (v i) (z : ℂ) =
          ∑ l, LaurentPolynomial.eval₂ (algebraicClosure ℚ ℂ).toSubfield.subtype z
            (B i l) * v l (z : ℂ)) ∧
        (∀ z : ℂˣ, ∀ i, (z : ℂ) * deriv (w i) (z : ℂ) =
          ∑ l, LaurentPolynomial.eval₂ (algebraicClosure ℚ ℂ).toSubfield.subtype z
            (B i l) * w l (z : ℂ)) ∧
        ∃ i j : Fin d, v i = f ∧ w j = g

/-- A numerical strict-E unit and its separately represented inverse both lie
in one finite frame-value algebra, conditional only on the named availability
input. Algebraic connection coefficients are derived by Stage21. -/
theorem strictEValueUnit_common_frame_values
    (hAndre : StrictECommonArithmeticFrameAvailability)
    (u : ℂ) (hu : IsStrictEValueUnit u) :
    ∃ d : ℕ,
    ∃ B : Matrix (Fin d) (Fin d) (LaurentPolynomial (algebraicClosure ℚ ℂ).toSubfield),
    ∃ M : Matrix (Fin d) (Fin d) (algebraicClosure ℚ ℂ).toSubfield,
    ∃ F : Matrix (Fin d) (Fin d)
      (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield),
      (∀ i j, IsStrictEFunction (F i j).val.val) ∧
      (∀ a : (algebraicClosure ℚ ℂ).toSubfield,
        (minpoly (algebraicClosure ℚ ℂ).toSubfield M).IsRoot a →
          ∃ q : ℚ, (q : (algebraicClosure ℚ ℂ).toSubfield) = a) ∧
      Stage17ActualEulerFrameRelation (algebraicClosure ℚ ℂ).toSubfield B M F ∧
      (F.map (stage14_subfieldEntireEvaluation (algebraicClosure ℚ ℂ).toSubfield 1)).det ≠ 0 ∧
      u ∈ Algebra.adjoin (algebraicClosure ℚ ℂ).toSubfield
        (Set.range fun ij : Fin d × Fin d => (F ij.1 ij.2).val.val 1) ∧
      u⁻¹ ∈ Algebra.adjoin (algebraicClosure ℚ ℂ).toSubfield
        (Set.range fun ij : Fin d × Fin d => (F ij.1 ij.2).val.val 1) := by
  obtain ⟨hu0, ⟨f, hf, hfu⟩, ⟨g, hg, hgu⟩⟩ := (strictEValueUnit_iff_at_one u).mp hu
  obtain ⟨d, B, M, F, hstrict, hrat, hF, h1, v, w, hv, hw, hvs, hws, i, j, hvi, hwj⟩ :=
    hAndre f g hf hg
  obtain ⟨c, hc⟩ := stage21_strictESolutionVector_value_coverage B M F v hv hrat hF hvs h1
  obtain ⟨b, hb⟩ := stage21_strictESolutionVector_value_coverage B M F w hw hrat hF hws h1
  refine ⟨d, B, M, F, hstrict, hrat, hF, h1, ?_, ?_⟩
  · exact value_mem_frameAlgebra_of_coordinates (algebraicClosure ℚ ℂ).toSubfield
      (fun a b => (F a b).val.val 1) c i u
        (hfu.symm.trans ((congrFun hvi 1).symm.trans (hc i)))
  · exact value_mem_frameAlgebra_of_coordinates (algebraicClosure ℚ ℂ).toSubfield
      (fun a b => (F a b).val.val 1) b j u⁻¹
        (hgu.symm.trans ((congrFun hwj 1).symm.trans (hb j)))

end StrictEUnit
#print axioms StrictEUnit.value_mem_frameAlgebra_of_coordinates
#print axioms StrictEUnit.StrictECommonArithmeticFrameAvailability
#print axioms StrictEUnit.strictEValueUnit_common_frame_values
