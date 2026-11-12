import Stage27ActualFrameAssembly

/-! Common frames are constructed from separately supplied per-function frames.
The per-function arithmetic normal-form existence input remains unproved. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

/-- A supplied actual arithmetic frame. This structure states its properties;
it does not assert that such a frame exists for an arbitrary strict E-function. -/
structure Stage27ArithmeticFrame (k : Subfield ℂ) (n : Type*)
    [Fintype n] [DecidableEq n] where
  B : Matrix n n (LaurentPolynomial k)
  M : Matrix n n k
  F : Matrix n n (subfieldEntireFunctionAlgebra k)
  strict : ∀ i j, IsStrictEFunction (F i j).val.val
  rational : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a
  relation : Stage17ActualEulerFrameRelation k B M F
  invertible_at_one : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0

/-- One literal original function occurs in an actual strict-E solution vector
of the supplied frame's system. No connection constants are supplied. -/
structure Stage27CoveredFunction (k : Subfield ℂ) {n : Type*}
    [Fintype n] [DecidableEq n] (D : Stage27ArithmeticFrame k n) (f : ℂ → ℂ) where
  v : n → ℂ → ℂ
  strict : ∀ i, IsStrictEFunction (v i)
  solution : Stage27ActualEulerSolution k D.B v
  component : n
  component_eq : v component = f

variable {k : Subfield ℂ} {n m r : Type*}
  [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

/-- Actual block-diagonal assembly of the two supplied arithmetic frames. -/
def stage27_blockFrame (D : Stage27ArithmeticFrame k n)
    (E : Stage27ArithmeticFrame k m) : Stage27ArithmeticFrame k (n ⊕ m) where
  B := Matrix.fromBlocks D.B 0 0 E.B
  M := Matrix.fromBlocks D.M 0 0 E.M
  F := Matrix.fromBlocks D.F 0 0 E.F
  strict := stage27_strictE_blockDiagonal k D.F E.F D.strict E.strict
  rational := stage27_blockDiagonal_rational_spectrum D.M E.M D.rational E.rational
  relation := stage27_actualEulerFrame_blockDiagonal k D.B E.B D.M E.M D.F E.F
    D.relation E.relation
  invertible_at_one := stage27_blockDiagonal_det_ne_zero k D.F E.F
    D.invertible_at_one E.invertible_at_one

/-- Finite reindexing transports every arithmetic frame property. -/
def stage27_reindexFrame (e : n ≃ r) (D : Stage27ArithmeticFrame k n) :
    Stage27ArithmeticFrame k r where
  B := Matrix.reindex e e D.B
  M := Matrix.reindex e e D.M
  F := Matrix.reindex e e D.F
  strict i j := D.strict (e.symm i) (e.symm j)
  rational a ha := D.rational a (by rwa [stage27_reindex_minpoly] at ha)
  relation := stage27_actualEulerFrame_reindex k e D.B D.M D.F D.relation
  invertible_at_one := stage27_reindex_det_ne_zero k e D.F D.invertible_at_one

/-- The original function in the first frame is unchanged in the common system. -/
def stage27_coverInl (D : Stage27ArithmeticFrame k n) (E : Stage27ArithmeticFrame k m)
    {f : ℂ → ℂ} (v : Stage27CoveredFunction k D f) :
    Stage27CoveredFunction k (stage27_blockFrame D E) f where
  v := Sum.elim v.v (fun _ _ => 0)
  strict i := by
    cases i with
    | inl i => exact v.strict i
    | inr i => simpa using algebraic_constant_isStrictEFunction (0 : AlgebraicComplex)
  solution := stage27_actualEulerSolution_inl k D.B E.B v.v v.solution
  component := Sum.inl v.component
  component_eq := v.component_eq

/-- The original function in the second frame is unchanged in the same common system. -/
def stage27_coverInr (D : Stage27ArithmeticFrame k n) (E : Stage27ArithmeticFrame k m)
    {g : ℂ → ℂ} (w : Stage27CoveredFunction k E g) :
    Stage27CoveredFunction k (stage27_blockFrame D E) g where
  v := Sum.elim (fun _ _ => 0) w.v
  strict i := by
    cases i with
    | inl i => simpa using algebraic_constant_isStrictEFunction (0 : AlgebraicComplex)
    | inr i => exact w.strict i
  solution := stage27_actualEulerSolution_inr k D.B E.B w.v w.solution
  component := Sum.inr w.component
  component_eq := w.component_eq

/-- Reindexing transports the solution and its literal original component together. -/
def stage27_reindexCover (e : n ≃ r) (D : Stage27ArithmeticFrame k n)
    {f : ℂ → ℂ} (v : Stage27CoveredFunction k D f) :
    Stage27CoveredFunction k (stage27_reindexFrame e D) f where
  v := v.v ∘ e.symm
  strict i := v.strict (e.symm i)
  solution := stage27_actualEulerSolution_reindex k e D.B v.v v.solution
  component := e v.component
  component_eq := by simpa using v.component_eq

/-- The remaining arithmetic existence input is now per function only: its
own actual frame and its own actual solution vector. No shared-system,
direct-sum, spectrum-closure or algebraic connection-coordinate input appears. -/
def Stage27IndividualArithmeticFrameAvailability : Prop :=
  ∀ f : ℂ → ℂ, IsStrictEFunction f →
    ∃ d : ℕ, ∃ D : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin d),
      Nonempty (Stage27CoveredFunction (algebraicClosure ℚ ℂ).toSubfield D f)

/-- Two independently supplied actual frames produce precisely the common-frame
availability package required by Stage24. Every assembly property is proved. -/
theorem stage27_commonFrameAvailability_of_individual
    (h : Stage27IndividualArithmeticFrameAvailability) :
    StrictECommonArithmeticFrameAvailability := by
  intro f g hf hg
  obtain ⟨d, D, ⟨v⟩⟩ := h f hf
  obtain ⟨e, E, ⟨w⟩⟩ := h g hg
  let s := Fintype.equivFin (Fin d ⊕ Fin e)
  let Q := stage27_reindexFrame s (stage27_blockFrame D E)
  let v' := stage27_reindexCover s (stage27_blockFrame D E) (stage27_coverInl D E v)
  let w' := stage27_reindexCover s (stage27_blockFrame D E) (stage27_coverInr D E w)
  exact ⟨_, Q.B, Q.M, Q.F, Q.strict, Q.rational, Q.relation, Q.invertible_at_one,
    v'.v, w'.v, v'.strict, w'.strict, v'.solution, w'.solution,
    v'.component, w'.component, v'.component_eq, w'.component_eq⟩

/-- Conversely, the old common package gives the per-function one by using f twice.
Thus the new input removes construction obligations, not arithmetic existence. -/
theorem stage27_individualFrameAvailability_of_common
    (h : StrictECommonArithmeticFrameAvailability) :
    Stage27IndividualArithmeticFrameAvailability := by
  intro f hf
  obtain ⟨d, B, M, F, hs, hr, hrel, hi, v, w, hv, hw, hvs, hws, i, j, he, he'⟩ :=
    h f f hf hf
  let D : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin d) :=
    ⟨B, M, F, hs, hr, hrel, hi⟩
  exact ⟨d, D, ⟨⟨v, hv, hvs, i, he⟩⟩⟩

/-- The two availability propositions are equivalent after the proved block construction.
Neither proposition is established unconditionally by this equivalence. -/
theorem stage27_commonFrameAvailability_iff_individual :
    StrictECommonArithmeticFrameAvailability ↔ Stage27IndividualArithmeticFrameAvailability :=
  ⟨stage27_individualFrameAvailability_of_common, stage27_commonFrameAvailability_of_individual⟩

end StrictEUnit
