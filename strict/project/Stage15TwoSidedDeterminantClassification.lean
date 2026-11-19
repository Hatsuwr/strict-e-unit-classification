import Stage15StrictEDeterminantClassification

/-! The two-sided matrix equation required by a changed fundamental frame:
p F' = A F - F C. This produces the actual determinant equation with trace
A minus trace C, and then arithmetic classification from proved nonvanishing. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Left multiplication contributes trace A to determinant variation. -/
theorem determinant_left_variation_eq_trace_mul {R n : Type*}
    [CommRing R] [Fintype n] [DecidableEq n] (A F : Matrix n n R) :
    (∑ i, (F.updateRow i (fun j => (A * F) i j)).det) = A.trace * F.det := by
  rw [Matrix.trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hrow : (fun j => (A * F) i j) = ∑ k, A i k • F k := by
    ext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  rfl

/-- Right multiplication contributes trace C to determinant variation. -/
theorem determinant_right_variation_eq_trace_mul {R n : Type*}
    [CommRing R] [Fintype n] [DecidableEq n] (C F : Matrix n n R) :
    (∑ j, (F.updateCol j (fun i => (F * C) i j)).det) = C.trace * F.det := by
  rw [Matrix.trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hcol : (fun i => (F * C) i j) = fun i => ∑ k, C k j • F i k := by
    ext i
    simp only [Matrix.mul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [hcol, Matrix.det_updateCol_sum, smul_eq_mul]
  rfl

/-- Abel's determinant equation for a genuine two-sided matrix equation,
without assuming that the solution matrix is invertible. -/
theorem derivation_det_two_sided {k R n : Type*}
    [CommRing k] [CommRing R] [Algebra k R] [Fintype n] [DecidableEq n]
    (δ : Derivation k R R) (A C F : Matrix n n R)
    (hF : matrixDerivative δ F = A * F - F * C) :
    δ F.det = (A.trace - C.trace) * F.det := by
  rw [derivation_det_rows]
  have hrow (i : n) : (fun j => δ (F i j)) =
      (fun j => (A * F) i j) - (fun j => (F * C) i j) := by
    ext j
    exact congrArg (fun M => M i j) hF
  have hsub (i : n) (u v : n → R) :
      (F.updateRow i (u-v)).det = (F.updateRow i u).det - (F.updateRow i v).det :=
    Matrix.detRowAlternating.map_update_sub F i u v
  simp_rw [hrow, hsub]
  rw [Finset.sum_sub_distrib,
    ← determinant_variation_rows_cols F (F * C),
    determinant_left_variation_eq_trace_mul, determinant_right_variation_eq_trace_mul,
    sub_mul]

/-- Scalar denominator-clearing preserves the two-sided trace formula. -/
theorem scaled_derivation_det_two_sided {k R n : Type*}
    [CommRing k] [CommRing R] [Algebra k R] [Fintype n] [DecidableEq n]
    (δ : Derivation k R R) (p : R) (A C F : Matrix n n R)
    (hF : ∀ i j, p * δ (F i j) = (A * F - F * C) i j) :
    p * δ F.det = (A.trace - C.trace) * F.det := by
  apply derivation_det_two_sided (p • δ) A C F
  ext i j
  exact hF i j

/-- The actual two-sided differential equation implies the scalar equation
for the actual entire determinant. -/
theorem entireMatrix_determinant_two_sided_firstOrder {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z) :
    ∀ z, p.val z * deriv F.det.val z =
      (A.trace.val z - C.trace.val z) * F.det.val z := by
  have hsystem : ∀ i j, p * entireFunctionDerivation (F i j) = (A * F - F * C) i j := by
    intro i j
    apply Subtype.ext
    funext z
    change p.val z * deriv (F i j).val z =
      entireEvaluation z ((∑ k, A i k * F k j) - ∑ k, F i k * C k j)
    simpa only [map_sub, map_sum, map_mul, entireEvaluation_apply] using hF z i j
  have hdet := scaled_derivation_det_two_sided entireFunctionDerivation p A C F hsystem
  intro z
  exact congrArg (fun g : entireFunctionAlgebra => g.val z) hdet

/-- The actual two-sided matrix identity only has to be supplied off zero.
Its denominator-cleared form extends to zero by continuity. -/
theorem entireMatrix_two_sided_extend_across_origin {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z) :
    ∀ z i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z := by
  intro z i j
  have hdf : Differentiable ℂ (deriv (F i j).val) :=
    differentiableOn_univ.mp ((F i j).property.differentiableOn.deriv isOpen_univ)
  have heval (w : ℂ) : ((A * F - F * C) i j).val w =
      (∑ k, (A i k).val w * (F k j).val w) -
        ∑ k, (F i k).val w * (C k j).val w := by
    change entireEvaluation w ((∑ k, A i k * F k j) - ∑ k, F i k * C k j) = _
    simp only [map_sub, map_sum, map_mul, entireEvaluation_apply]
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (p.property.continuous.mul hdf.continuous) ((A * F - F * C) i j).property.continuous
    (fun w hw => (hF w hw i j).trans (heval w).symm)
  exact (congrFun heq z).trans (heval z)

/-- One nonzero determinant and regular leading coefficient prove
nonvanishing off zero for an actual punctured two-sided system. -/
theorem entireMatrix_two_sided_determinant_nonzero_off_origin {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → (F.map (entireEvaluation z)).det ≠ 0 := by
  have hode := entireMatrix_determinant_two_sided_firstOrder p A C F
    (entireMatrix_two_sided_extend_across_origin p A C F hF)
  rw [← entireMatrix_evaluation_det] at h1
  intro z hz
  rw [← entireMatrix_evaluation_det]
  exact entire_firstOrder_nonzero_at_regular p.property
    (A.trace.property.sub C.trace.property) F.det.property hode h1 (hp z hz)

/-- The precise two-sided determinant endpoint: actual strict-E entries,
a punctured denominator-cleared system, regularity, and one nonzero value
supply the arithmetic determinant normal form. -/
theorem strictE_entireMatrix_two_sided_determinant_exp_form {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    ∃ m : ℕ, ∃ c a : AlgebraicComplex,
      (F.det.property.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient F.det.val m ∧
      ∀ z, (F.map (entireEvaluation z)).det =
        (c : ℂ) * z^m * Complex.exp ((a : ℂ)*z) := by
  have hf := strictEFunction_entireMatrix_det F hstrict
  have hnz : ∀ z : ℂ, z ≠ 0 → F.det.val z ≠ 0 := by
    intro z hz
    rw [entireMatrix_evaluation_det]
    exact entireMatrix_two_sided_determinant_nonzero_off_origin p A C F hF hp h1 z hz
  obtain ⟨m, c, a, hm, hc, hcoeff, hform⟩ :=
    strictEFunction_origin_only_zero_exp_form hf hnz
  refine ⟨m, c, a, hm, hc, hcoeff, fun z => ?_⟩
  rw [← entireMatrix_evaluation_det]
  exact hform z

/-- The resulting determinant value is a unit of the actual numerical
strict-E ring, including a genuine reciprocal representative. -/
theorem strictE_entireMatrix_two_sided_determinant_at_one_unit {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    IsStrictEValueUnit ((F.map (entireEvaluation 1)).det) := by
  rw [← entireMatrix_evaluation_det]
  apply strictEFunction_at_one_unit_of_origin_only_zeros (strictEFunction_entireMatrix_det F hstrict)
  intro z hz
  rw [entireMatrix_evaluation_det]
  exact entireMatrix_two_sided_determinant_nonzero_off_origin p A C F hF hp h1 z hz

/-- Euler-system specialization for the changed-frame equation
z F' = A F - F C. Regularity off zero is now proved for the actual coordinate,
not left as a separate hypothesis. The frame and its equation remain inputs. -/
theorem strictE_entireMatrix_euler_two_sided_determinant_exp_form {n : Type*}
    [Fintype n] [DecidableEq n]
    (A C F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z, z ≠ 0 → ∀ i j, z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) -
        ∑ k, (F i k).val z * (C k j).val z)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    ∃ m : ℕ, ∃ c a : AlgebraicComplex,
      (F.det.property.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient F.det.val m ∧
      ∀ z, (F.map (entireEvaluation z)).det =
        (c : ℂ) * z^m * Complex.exp ((a : ℂ)*z) :=
  strictE_entireMatrix_two_sided_determinant_exp_form entireCoordinate A C F hstrict hF
    (fun z hz => hz) h1

end StrictEUnit
