import Stage27BlockFrameAlgebra

/-! Actual analytic frame and solution equations under block sums and reindexing.
All zero entries, derivatives, finite sums and determinant identities are proved. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

variable (k : Subfield ℂ) {n m r : Type*}
  [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

/-- The literal actual Euler solution equation at nonzero complex arguments. -/
def Stage27ActualEulerSolution (B : Matrix n n (LaurentPolynomial k))
    (v : n → ℂ → ℂ) : Prop :=
  ∀ z : ℂˣ, ∀ i, (z : ℂ) * deriv (v i) (z : ℂ) =
    ∑ l, LaurentPolynomial.eval₂ k.subtype z (B i l) * v l (z : ℂ)

omit [DecidableEq n] [DecidableEq m] in
/-- Block diagonals satisfy the actual analytic two-sided frame equation. -/
theorem stage27_actualEulerFrame_blockDiagonal
    (B : Matrix n n (LaurentPolynomial k)) (C : Matrix m m (LaurentPolynomial k))
    (M : Matrix n n k) (N : Matrix m m k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (G : Matrix m m (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (hG : Stage17ActualEulerFrameRelation k C N G) :
    Stage17ActualEulerFrameRelation k (Matrix.fromBlocks B 0 0 C)
      (Matrix.fromBlocks M 0 0 N) (Matrix.fromBlocks F 0 0 G) := by
  intro z i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [Fintype.sum_sum_type] using hF z i j
    | inr j => simp [Fintype.sum_sum_type]
  | inr i =>
    cases j with
    | inl j => simp [Fintype.sum_sum_type]
    | inr j => simpa [Fintype.sum_sum_type] using hG z i j

omit [DecidableEq n] [DecidableEq m] in
/-- Zero padding on the right preserves an actual solution and its original block. -/
theorem stage27_actualEulerSolution_inl
    (B : Matrix n n (LaurentPolynomial k)) (C : Matrix m m (LaurentPolynomial k))
    (v : n → ℂ → ℂ) (hv : Stage27ActualEulerSolution k B v) :
    Stage27ActualEulerSolution k (Matrix.fromBlocks B 0 0 C)
      (Sum.elim v (fun _ _ => 0)) := by
  intro z i
  cases i with
  | inl i => simpa [Fintype.sum_sum_type] using hv z i
  | inr i => simp [Fintype.sum_sum_type]

omit [DecidableEq n] [DecidableEq m] in
/-- Zero padding on the left preserves an actual solution and its original block. -/
theorem stage27_actualEulerSolution_inr
    (B : Matrix n n (LaurentPolynomial k)) (C : Matrix m m (LaurentPolynomial k))
    (w : m → ℂ → ℂ) (hw : Stage27ActualEulerSolution k C w) :
    Stage27ActualEulerSolution k (Matrix.fromBlocks B 0 0 C)
      (Sum.elim (fun _ _ => 0) w) := by
  intro z i
  cases i with
  | inl i => simp [Fintype.sum_sum_type]
  | inr i => simpa [Fintype.sum_sum_type] using hw z i

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- The actual block frame remains strict E entry by entry, including its zeros. -/
theorem stage27_strictE_blockDiagonal
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (G : Matrix m m (subfieldEntireFunctionAlgebra k))
    (hF : ∀ i j, IsStrictEFunction (F i j).val.val)
    (hG : ∀ i j, IsStrictEFunction (G i j).val.val) :
    ∀ i j, IsStrictEFunction ((Matrix.fromBlocks F 0 0 G) i j).val.val := by
  have hz : IsStrictEFunction (fun _ : ℂ => (0 : ℂ)) := by
    simpa using algebraic_constant_isStrictEFunction (0 : AlgebraicComplex)
  intro i j
  cases i <;> cases j
  · exact hF _ _
  · exact hz
  · exact hz
  · exact hG _ _

/-- Evaluation and the block determinant formula give actual invertibility at one. -/
theorem stage27_blockDiagonal_det_ne_zero
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (G : Matrix m m (subfieldEntireFunctionAlgebra k))
    (hF : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0)
    (hG : (G.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ((Matrix.fromBlocks F 0 0 G).map
      (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 := by
  rw [Matrix.fromBlocks_map]
  simp only [Matrix.map_zero _ (map_zero _)]
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero hF hG

omit [DecidableEq n] [DecidableEq r] in
/-- The actual frame relation survives arbitrary finite equivalence reindexing. -/
theorem stage27_actualEulerFrame_reindex (e : n ≃ r)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    Stage17ActualEulerFrameRelation k (Matrix.reindex e e B)
      (Matrix.reindex e e M) (Matrix.reindex e e F) := by
  intro z i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun l => LaurentPolynomial.eval₂ k.subtype z
    (B (e.symm i) l) * (F l (e.symm j)).val.val (z : ℂ)),
    e.symm.sum_comp (fun l => (F (e.symm i) l).val.val (z : ℂ) *
      (M l (e.symm j) : ℂ))]
  exact hF z (e.symm i) (e.symm j)

omit [DecidableEq n] [DecidableEq r] in
/-- The solution relation survives the same finite equivalence reindexing. -/
theorem stage27_actualEulerSolution_reindex (e : n ≃ r)
    (B : Matrix n n (LaurentPolynomial k)) (v : n → ℂ → ℂ)
    (hv : Stage27ActualEulerSolution k B v) :
    Stage27ActualEulerSolution k (Matrix.reindex e e B) (v ∘ e.symm) := by
  intro z i
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  rw [e.symm.sum_comp (fun l => LaurentPolynomial.eval₂ k.subtype z
    (B (e.symm i) l) * v l (z : ℂ))]
  exact hv z (e.symm i)

/-- Actual evaluated invertibility is invariant under finite index transport. -/
theorem stage27_reindex_det_ne_zero (e : n ≃ r)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ((Matrix.reindex e e F).map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 := by
  change (Matrix.reindex e e (F.map (stage14_subfieldEntireEvaluation k 1))).det ≠ 0
  rwa [Matrix.det_reindex_self]

end StrictEUnit
