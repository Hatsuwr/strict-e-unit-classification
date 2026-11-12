import FormalPolynomialImage

/-! Evaluation of the formal logarithm coordinate is constructed only on a
polynomial image with an actual coefficient evaluation. No arbitrary Laurent
series or rational function is evaluated analytically. -/
noncomputable section
namespace StrictEUnit
variable {k L K : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing K] [Algebra k K]

/-- Extend an actual coefficient evaluation to its formal polynomial image,
setting the log variable to zero. -/
def formalPolynomialImageEvaluation (S : Subalgebra k L) (ν : S →ₐ[k] K) :
    (formalPolynomialEmbedding S).range →ₐ[k] K :=
  (Polynomial.eval₂AlgHom' ν 0 (fun _ => Commute.all _ _)).comp
    (formalPolynomialImageEquiv S).symm.toAlgHom

@[simp] theorem formalPolynomialImageEvaluation_polynomial
    (S : Subalgebra k L) (ν : S →ₐ[k] K) (p : Polynomial S) :
    formalPolynomialImageEvaluation S ν (formalPolynomialImageEquiv S p) =
      p.eval₂ ν.toRingHom 0 := by
  simp [formalPolynomialImageEvaluation]

/-- The resulting map agrees with the supplied coefficient map. -/
theorem formalPolynomialImageEvaluation_constant
    (S : Subalgebra k L) (ν : S →ₐ[k] K)
    (u : (formalPolynomialEmbedding S).range) (s : S)
    (h : (u : RatFunc L) = RatFunc.C (s : L)) :
    formalPolynomialImageEvaluation S ν u = ν s := by
  have hu : u = formalPolynomialImageEquiv S (Polynomial.C s) := by
    apply Subtype.ext
    exact h.trans (formalPolynomialEmbedding_C S s).symm
  rw [hu, formalPolynomialImageEvaluation_polynomial]
  simp

/-- In particular, the actual image of the formal log coordinate evaluates to zero. -/
theorem formalPolynomialImageEvaluation_variable
    (S : Subalgebra k L) (ν : S →ₐ[k] K)
    (u : (formalPolynomialEmbedding S).range)
    (h : (u : RatFunc L) = RatFunc.X) :
    formalPolynomialImageEvaluation S ν u = 0 := by
  have hu : u = formalPolynomialImageEquiv S Polynomial.X := by
    apply Subtype.ext
    exact h.trans (formalPolynomialEmbedding_X S).symm
  rw [hu, formalPolynomialImageEvaluation_polynomial]
  simp

/-- Transport the actual evaluation through a proved equality of subalgebras. -/
def formalPolynomialEvaluationOfEq (S : Subalgebra k L)
    (R : Subalgebra k (RatFunc L))
    (hR : R = (formalPolynomialEmbedding S).range) (ν : S →ₐ[k] K) :
    R →ₐ[k] K :=
  (formalPolynomialImageEvaluation S ν).comp (Subalgebra.equivOfEq _ _ hR).toAlgHom

theorem formalPolynomialEvaluationOfEq_constant (S : Subalgebra k L)
    (R : Subalgebra k (RatFunc L))
    (hR : R = (formalPolynomialEmbedding S).range) (ν : S →ₐ[k] K)
    (u : R) (s : S) (h : (u : RatFunc L) = RatFunc.C (s : L)) :
    formalPolynomialEvaluationOfEq S R hR ν u = ν s :=
  formalPolynomialImageEvaluation_constant S ν _ s h

theorem formalPolynomialEvaluationOfEq_variable (S : Subalgebra k L)
    (R : Subalgebra k (RatFunc L))
    (hR : R = (formalPolynomialEmbedding S).range) (ν : S →ₐ[k] K)
    (u : R) (h : (u : RatFunc L) = RatFunc.X) :
    formalPolynomialEvaluationOfEq S R hR ν u = 0 :=
  formalPolynomialImageEvaluation_variable S ν _ h

end StrictEUnit
#print axioms StrictEUnit.formalPolynomialImageEvaluation
#print axioms StrictEUnit.formalPolynomialImageEvaluation_polynomial
#print axioms StrictEUnit.formalPolynomialImageEvaluation_constant
#print axioms StrictEUnit.formalPolynomialImageEvaluation_variable
#print axioms StrictEUnit.formalPolynomialEvaluationOfEq
#print axioms StrictEUnit.formalPolynomialEvaluationOfEq_constant
#print axioms StrictEUnit.formalPolynomialEvaluationOfEq_variable
