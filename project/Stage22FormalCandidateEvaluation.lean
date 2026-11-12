import Stage22PolynomialImageEvaluation
import FormalMatrixLogRemoval

/-! A numerical algebra map on the whole actual formal matrix candidate,
constructed from an actual coefficient-algebra evaluation and the proved
polynomial-image identity. Its existence is not fiber injectivity. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The base-unit changed candidate is literally the same polynomial image. -/
theorem formalMatrix_baseChange_polynomial_image
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    (matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))).restrictScalars k =
      (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range := by
  rw [matrixGeneratedAlgebra_mul_base_unit]
  exact formalMatrix_candidate_eq_polynomial_image F

/-- The actual algebra map on the whole base-unit changed candidate. -/
def formalMatrixCandidateEvaluation
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K) :
    matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))) →ₐ[k] K :=
  formalPolynomialEvaluationOfEq (formalMatrixCoefficientAlgebra F) _
    (formalMatrix_baseChange_polynomial_image F Z) ν

/-- Formal coefficient equality gives numerical compatibility, without
attempting to evaluate any arbitrary Laurent series. -/
theorem formalMatrixCandidateEvaluation_coefficient
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K)
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))))
    (s : formalMatrixCoefficientAlgebra F)
    (h : (u : RatFunc (LaurentSeries k)) = RatFunc.C (s : LaurentSeries k)) :
    formalMatrixCandidateEvaluation F Z ν u = ν s :=
  formalPolynomialEvaluationOfEq_constant _ _ _ _ _ _ h

/-- The formal log coordinate has actual image zero under this evaluation. -/
theorem formalMatrixCandidateEvaluation_log
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K)
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))))
    (h : (u : RatFunc (LaurentSeries k)) = RatFunc.X) :
    formalMatrixCandidateEvaluation F Z ν u = 0 :=
  formalPolynomialEvaluationOfEq_variable _ _ _ _ _ h

/-- Log removal and the constructed numerical map use the same coefficient
unit. This transports a separately proved coefficient-unit classification. -/
theorem formalMatrixCandidateEvaluation_unit
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K)
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))))
    (hu : IsUnit u) :
    ∃ s : formalMatrixCoefficientAlgebra F, IsUnit s ∧
      RatFunc.C (s : LaurentSeries k) = (u : RatFunc (LaurentSeries k)) ∧
      formalMatrixCandidateEvaluation F Z ν u = ν s := by
  obtain ⟨s, hs, he⟩ := formalMatrix_base_change_unit_is_coefficient F Z u hu
  exact ⟨s, hs, he, formalMatrixCandidateEvaluation_coefficient F Z ν u s he.symm⟩

end StrictEUnit
#print axioms StrictEUnit.formalMatrix_baseChange_polynomial_image
#print axioms StrictEUnit.formalMatrixCandidateEvaluation
#print axioms StrictEUnit.formalMatrixCandidateEvaluation_coefficient
#print axioms StrictEUnit.formalMatrixCandidateEvaluation_log
#print axioms StrictEUnit.formalMatrixCandidateEvaluation_unit
