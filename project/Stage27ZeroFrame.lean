import Stage27PerFunctionFrameAvailability

/-! The zero-function edge case needs no arithmetic existence input. -/
noncomputable section
namespace StrictEUnit

/-- A concrete rank-one frame for the trivial Euler equation. -/
def stage27_trivialFrame (k : Subfield ℂ) : Stage27ArithmeticFrame k (Fin 1) where
  B := 0
  M := 0
  F := 1
  strict i j := by
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simpa using algebraic_constant_isStrictEFunction (1 : AlgebraicComplex)
  rational a ha := by
    have h : a = 0 := by simpa using ha
    exact ⟨0, by simpa using h.symm⟩
  relation := by
    intro z i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp
  invertible_at_one := by simp

/-- The zero function is literally the component of the zero solution vector. -/
def stage27_zeroCover (k : Subfield ℂ) :
    Stage27CoveredFunction k (stage27_trivialFrame k) (fun _ => 0) where
  v := fun _ _ => 0
  strict i := by simpa using algebraic_constant_isStrictEFunction (0 : AlgebraicComplex)
  solution := by intro z i; simp
  component := 0
  component_eq := rfl

/-- A still smaller existence input may be restricted to nonzero strict E-functions. -/
def Stage27NonzeroIndividualArithmeticFrameAvailability : Prop :=
  ∀ f : ℂ → ℂ, IsStrictEFunction f → f ≠ (fun _ => 0) →
    ∃ d : ℕ, ∃ D : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin d),
      Nonempty (Stage27CoveredFunction (algebraicClosure ℚ ℂ).toSubfield D f)

/-- The explicit rank-one zero frame removes any zero-function input obligation. -/
theorem stage27_individualAvailability_of_nonzero
    (h : Stage27NonzeroIndividualArithmeticFrameAvailability) :
    Stage27IndividualArithmeticFrameAvailability := by
  intro f hf
  by_cases hz : f = (fun _ => 0)
  · subst f
    exact ⟨1, stage27_trivialFrame _, ⟨stage27_zeroCover _⟩⟩
  · exact h f hf hz

/-- Common actual arithmetic frames follow from per-function existence for
nonzero strict E-functions alone; all zero and assembly cases are constructed. -/
theorem stage27_commonAvailability_of_nonzero_individual
    (h : Stage27NonzeroIndividualArithmeticFrameAvailability) :
    StrictECommonArithmeticFrameAvailability :=
  stage27_commonFrameAvailability_of_individual (stage27_individualAvailability_of_nonzero h)

end StrictEUnit
