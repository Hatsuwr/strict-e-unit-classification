import Stage17FormalBaseUnitData
import Stage17ArithmeticFrameODE
import Stage16AlgebraicCoefficientField

/-!
# Constructed formal fundamental matrix from an actual arithmetic frame

The André frame itself is an explicit analytic input. The theorem constructs
positive ramification and the logarithmic base unit from the actual constant
matrix, then proves the formal ODE of Y = Taylor(F(t^N)) Z. Nonzero determinant
uses only the actual value det F(1), not an evaluation of arbitrary Laurent
series or a global zero-free premise.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit
local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of the genuine ramified formal frame is nonzero if its
actual determinant at one is nonzero. -/
theorem stage17_formalFrame_det_ne_zero (N : ℕ) (hN : N ≠ 0)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    (stage17_formalFrame k N hN F).det ≠ 0 := by
  intro hz
  have hdet : stage17_entireFormalAlgHom k
      (stage17_arithmeticPowerPullback k N hN F.det) = 0 := by
    rw [← hz]
    exact RingHom.map_det (stage17_ramifiedEntireFormalAlgHom k N hN).toRingHom F
  have heq := stage17_entireFormalAlgHom_injective k
    (hdet.trans (map_zero (stage17_entireFormalAlgHom k)).symm)
  have hv := congrArg (stage14_subfieldEntireEvaluation k 1) heq
  apply h1
  have hev : stage14_subfieldEntireEvaluation k 1 F.det =
      (F.map (stage14_subfieldEntireEvaluation k 1)).det :=
    RingHom.map_det (stage14_subfieldEntireEvaluation k 1).toRingHom F
  rw [← hev]
  change F.det.val.val 1 = 0
  change (stage17_arithmeticPowerPullback k N hN F.det).val.val 1 = 0 at hv
  simpa only [stage17_arithmeticPowerPullback_at_one] using hv

/- Embed an actual base matrix unit into the fixed formal ambient field. -/

/-- The genuinely constructed product matrix. -/
def stage17_formalFundamental (N : ℕ) (hN : N ≠ 0)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    Matrix n n (RatFunc (LaurentSeries k)) :=
  stage17_formalFrame k N hN F * (stage17_formalBaseMatrixUnit k Z : Matrix n n _)

/-- Differential compatibility of the genuine base embedding transfers the
constructed constant-matrix equation, without assuming it in the ambient field. -/
theorem stage17_formalBaseMatrixUnit_ode (N : ℕ) (hN : N ≠ 0)
    (M : Matrix n n k) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative (manuscriptBaseDerivation (k := k) N)
      (Z : Matrix n n (LaurentLogBase k)) =
        ramifiedConstantMatrix M * (Z : Matrix n n (LaurentLogBase k))) :
    matrixDerivative (formalAmbientDerivation N hN)
      (stage17_formalBaseMatrixUnit k Z : Matrix n n _) =
      M.map (algebraMap k (RatFunc (LaurentSeries k))) *
        (stage17_formalBaseMatrixUnit k Z : Matrix n n _) := by
  change matrixDerivative (formalAmbientDerivation N hN)
    (formalBaseEmbedding.toRingHom.mapMatrix (Z : Matrix n n (LaurentLogBase k))) = _
  have hmap : matrixDerivative (formalAmbientDerivation N hN)
      (formalBaseEmbedding.toRingHom.mapMatrix (Z : Matrix n n (LaurentLogBase k))) =
      formalBaseEmbedding.toRingHom.mapMatrix
        (matrixDerivative (manuscriptBaseDerivation (k := k) N)
          (Z : Matrix n n (LaurentLogBase k))) := by
    ext i j
    exact formalBaseEmbedding_differential N hN (Z.val i j)
  rw [hmap, hZ, map_mul]
  congr 1
  ext i j
  exact formalBaseEmbedding.commutes (M i j)

/-- Product rule cancels the right residue matrix and yields the literal
ramified Laurent system D_N Y = B(t^N)Y. -/
theorem stage17_formalFundamental_ode (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative (manuscriptBaseDerivation (k := k) N)
      (Z : Matrix n n (LaurentLogBase k)) =
        ramifiedConstantMatrix M * (Z : Matrix n n (LaurentLogBase k))) :
    matrixDerivative (formalAmbientDerivation N hN)
      (stage17_formalFundamental k N hN F Z) =
      (B.map (stage17_laurentBasePullback k N)).map formalBaseEmbedding *
        stage17_formalFundamental k N hN F Z := by
  rw [stage17_formalFundamental, matrixDerivative_mul,
    stage17_formalFrame_ode k N hN B M F hF,
    stage17_formalBaseMatrixUnit_ode k N hN M Z hZ]
  simp only [sub_mul, mul_assoc, sub_add_cancel]
  rfl

/-- The constructed formal fundamental matrix is invertible in the actual
ambient matrix ring, using only nonzero actual determinant at one. -/
theorem stage17_formalFundamental_isUnit (N : ℕ) (hN : N ≠ 0)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0)
    (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    IsUnit (stage17_formalFundamental k N hN F Z) := by
  apply IsUnit.mul
  · exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (stage17_formalFrame_det_ne_zero k N hN F h1))
  · exact (stage17_formalBaseMatrixUnit k Z).isUnit

/-- Positive ramification, the normalized logarithmic base unit, its exact
constant-matrix equation, and an invertible fundamental matrix are all obtained
from the actual frame and rational spectrum. No formal ODE is an input. -/
theorem stage17_actualFrame_exists_formalFundamental [IsAlgClosed k]
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a)
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ∃ N : ℕ, ∃ hN : N ≠ 0, ∃ Z : (Matrix n n (LaurentLogBase k))ˣ,
      matrixDerivative (manuscriptBaseDerivation (k := k) N)
        (Z : Matrix n n (LaurentLogBase k)) =
          ramifiedConstantMatrix M * (Z : Matrix n n (LaurentLogBase k)) ∧
      (laurentLogBasePoint k).toRingHom.mapMatrix (Z : Matrix n n (LaurentLogBase k)) = 1 ∧
      IsUnit (stage17_formalFundamental k N hN F Z) ∧
      matrixDerivative (formalAmbientDerivation N hN)
        (stage17_formalFundamental k N hN F Z) =
        (B.map (stage17_laurentBasePullback k N)).map formalBaseEmbedding *
          stage17_formalFundamental k N hN F Z := by
  obtain ⟨N, hN, Z, hZ, hpoint⟩ := stage15_rational_matrix_fundamental_unit M hrat
  exact ⟨N, Nat.ne_of_gt hN, Z, hZ, hpoint,
    stage17_formalFundamental_isUnit k N (Nat.ne_of_gt hN) F h1 Z,
    stage17_formalFundamental_ode k N (Nat.ne_of_gt hN) B M F hF Z hZ⟩

/-- The exact subfield used by the genuine arithmetic Taylor algebra is
algebraically closed, using the proved algebraic-number-field theorem. -/
theorem stage17_algebraicTaylorField_isAlgClosed :
    IsAlgClosed (algebraicClosure ℚ ℂ).toSubfield :=
  algebraicComplex_isAlgClosed

/-- Specialization to the exact algebraic-number subfield used by the Taylor
realization, with algebraic closedness discharged rather than assumed. -/
theorem stage17_algebraicFrame_exists_formalFundamental
    (B : Matrix n n (LaurentPolynomial (algebraicClosure ℚ ℂ).toSubfield))
    (M : Matrix n n (algebraicClosure ℚ ℂ).toSubfield)
    (F : Matrix n n (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield))
    (hrat : ∀ a : (algebraicClosure ℚ ℂ).toSubfield,
      (minpoly (algebraicClosure ℚ ℂ).toSubfield M).IsRoot a →
      ∃ q : ℚ, (q : (algebraicClosure ℚ ℂ).toSubfield) = a)
    (hF : Stage17ActualEulerFrameRelation (algebraicClosure ℚ ℂ).toSubfield B M F)
    (h1 : (F.map (stage14_subfieldEntireEvaluation (algebraicClosure ℚ ℂ).toSubfield 1)).det ≠ 0) :
    ∃ N : ℕ, ∃ hN : N ≠ 0,
      ∃ Z : (Matrix n n (LaurentLogBase (algebraicClosure ℚ ℂ).toSubfield))ˣ,
      matrixDerivative (manuscriptBaseDerivation (k := (algebraicClosure ℚ ℂ).toSubfield) N)
        (Z : Matrix n n (LaurentLogBase (algebraicClosure ℚ ℂ).toSubfield)) =
          ramifiedConstantMatrix M *
            (Z : Matrix n n (LaurentLogBase (algebraicClosure ℚ ℂ).toSubfield)) ∧
      (laurentLogBasePoint (algebraicClosure ℚ ℂ).toSubfield).toRingHom.mapMatrix
        (Z : Matrix n n (LaurentLogBase (algebraicClosure ℚ ℂ).toSubfield)) = 1 ∧
      IsUnit (stage17_formalFundamental (algebraicClosure ℚ ℂ).toSubfield N hN F Z) ∧
      matrixDerivative (formalAmbientDerivation N hN)
        (stage17_formalFundamental (algebraicClosure ℚ ℂ).toSubfield N hN F Z) =
        (B.map (stage17_laurentBasePullback (algebraicClosure ℚ ℂ).toSubfield N)).map
            formalBaseEmbedding *
          stage17_formalFundamental (algebraicClosure ℚ ℂ).toSubfield N hN F Z := by
  letI : IsAlgClosed (algebraicClosure ℚ ℂ).toSubfield :=
    stage17_algebraicTaylorField_isAlgClosed
  exact stage17_actualFrame_exists_formalFundamental (algebraicClosure ℚ ℂ).toSubfield
    B M F hrat hF h1

end StrictEUnit
