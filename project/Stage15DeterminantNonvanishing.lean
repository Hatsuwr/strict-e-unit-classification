import Stage15FirstOrderNonvanishing
import DeterminantalIdealStability
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Abel's determinant equation over a differential ring, followed by genuine
analytic nonvanishing. No fundamental matrix or arithmetic frame is postulated
as a constructed object in this module. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The scalar determinant ODE follows from a matrix equation, without an
invertible-matrix assumption or an assumed inverse determinant. -/
theorem derivation_det_eq_trace_mul {k R n : Type*}
    [CommRing k] [CommRing R] [Algebra k R] [Fintype n] [DecidableEq n]
    (δ : Derivation k R R) (A F : Matrix n n R)
    (hF : matrixDerivative δ F = A * F) :
    δ F.det = A.trace * F.det := by
  rw [derivation_det_rows, Matrix.trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hrow : (fun j => δ (F i j)) = ∑ k, A i k • F k := by
    funext j
    simpa only [matrixDerivative_apply, Matrix.mul_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using congrArg (fun M => M i j) hF
  rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  rfl

/-- Clearing a scalar denominator in the matrix system clears the same
scalar denominator in its determinant equation. -/
theorem scaled_derivation_det_eq_trace_mul {k R n : Type*}
    [CommRing k] [CommRing R] [Algebra k R] [Fintype n] [DecidableEq n]
    (δ : Derivation k R R) (p : R) (A F : Matrix n n R)
    (hF : ∀ i j, p * δ (F i j) = (A * F) i j) :
    p * δ F.det = A.trace * F.det := by
  have hscaled : matrixDerivative (p • δ) F = A * F := by
    ext i j
    exact hF i j
  exact derivation_det_eq_trace_mul (p • δ) A F hscaled

/-- Evaluation of the determinant in the entire-function algebra is the
ordinary determinant of the evaluated complex matrix. -/
theorem entireMatrix_evaluation_det {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n entireFunctionAlgebra) (z : ℂ) :
    F.det.val z = (F.map (entireEvaluation z)).det :=
  RingHom.map_det (entireEvaluation z).toRingHom F

/-- An actual matrix differential equation implies the actual first-order
scalar equation for its determinant. -/
theorem entireMatrix_determinant_firstOrder {n : Type*} [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z) :
    ∀ z, p.val z * deriv F.det.val z = A.trace.val z * F.det.val z := by
  have hsystem : ∀ i j, p * entireFunctionDerivation (F i j) = (A * F) i j := by
    intro i j
    apply Subtype.ext
    funext z
    change p.val z * deriv (F i j).val z =
      entireEvaluation z (∑ k, A i k * F k j)
    simpa only [map_sum, map_mul, entireEvaluation_apply] using hF z i j
  have hdet := scaled_derivation_det_eq_trace_mul entireFunctionDerivation p A F hsystem
  intro z
  exact congrArg (fun g : entireFunctionAlgebra => g.val z) hdet

/-- One known nonzero determinant makes it nonzero at every ordinary point
of an actual entire matrix system. -/
theorem entireMatrix_determinant_nonzero_at_regular {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z)
    {d : ℂ} (hd : (F.map (entireEvaluation d)).det ≠ 0)
    {c : ℂ} (hc : p.val c ≠ 0) : (F.map (entireEvaluation c)).det ≠ 0 := by
  rw [← entireMatrix_evaluation_det] at hd ⊢
  exact entire_firstOrder_nonzero_at_regular p.property A.trace.property F.det.property
    (entireMatrix_determinant_firstOrder p A F hF) hd hc

/-- The only possible determinant zero is at the singular origin when the
leading coefficient is regular everywhere else and the determinant at one
is nonzero. -/
theorem entireMatrix_determinant_nonzero_off_origin {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → (F.map (entireEvaluation z)).det ≠ 0 := by
  intro z hz
  exact entireMatrix_determinant_nonzero_at_regular p A F hF h1 (hp z hz)

/-- A denominator-cleared matrix equation checked only on the punctured
plane extends to the origin by continuity of its actual entire entries. -/
theorem entireMatrix_system_extend_across_origin {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z) :
    ∀ z i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z := by
  intro z i j
  have hdf : Differentiable ℂ (deriv (F i j).val) :=
    differentiableOn_univ.mp ((F i j).property.differentiableOn.deriv isOpen_univ)
  have heval (w : ℂ) : ((A * F) i j).val w =
      ∑ k, (A i k).val w * (F k j).val w := by
    change entireEvaluation w (∑ k, A i k * F k j) = _
    simp only [map_sum, map_mul, entireEvaluation_apply]
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (p.property.continuous.mul hdf.continuous) ((A * F) i j).property.continuous
    (fun w hw => (hF w hw i j).trans (heval w).symm)
  exact (congrFun heq z).trans (heval z)

/-- The determinant nonvanishing theorem applies to a matrix system imposed
only away from its possible singular point at zero. -/
theorem entireMatrix_determinant_nonzero_off_origin_of_punctured {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → (F.map (entireEvaluation z)).det ≠ 0 :=
  entireMatrix_determinant_nonzero_off_origin p A F
    (entireMatrix_system_extend_across_origin p A F hF) hp h1

end StrictEUnit
