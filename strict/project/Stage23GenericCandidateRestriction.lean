import Stage22FormalCandidateEvaluation

/-! Restriction of the already constructed candidate evaluation to a genuine
subalgebra. The coefficient matrix stays abstract in this algebraic wrapper. -/
noncomputable section
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra G →ₐ[k] K)
    (R : Subalgebra (LaurentLogBase k) (RatFunc (LaurentSeries k)))
    (hR : R ≤ matrixGeneratedAlgebra (B:=LaurentLogBase k)
      ((G.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))))

/-- Restrict the existing numerical map, without constructing a new realization. -/
def stage23_genericCandidateRestriction : R →ₐ[k] K :=
  (formalMatrixCandidateEvaluation G Z ν).comp ((Subalgebra.inclusion hR).restrictScalars k)

/-- Every coefficient represented in the subalgebra retains its actual value. -/
theorem stage23_genericCandidateRestriction_coefficient (r : R)
    (s : formalMatrixCoefficientAlgebra G)
    (h : (r : RatFunc (LaurentSeries k)) = RatFunc.C (s : LaurentSeries k)) :
    stage23_genericCandidateRestriction G Z ν R hR r = ν s :=
  formalMatrixCandidateEvaluation_coefficient G Z ν (Subalgebra.inclusion hR r) s h

/-- The restriction sends the represented log coordinate to zero. -/
theorem stage23_genericCandidateRestriction_log (r : R)
    (h : (r : RatFunc (LaurentSeries k)) = RatFunc.X) :
    stage23_genericCandidateRestriction G Z ν R hR r = 0 :=
  formalMatrixCandidateEvaluation_log G Z ν (Subalgebra.inclusion hR r) h

end StrictEUnit
