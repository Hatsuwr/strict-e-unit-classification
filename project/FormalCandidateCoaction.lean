import FaithfullyFlatCandidateCoaction
import FormalAmbientDifferentialField

/-! The actual formal ambient field and its actual embedded manuscript base.
Only an invertible solution matrix in that formal field remains supplied.
No existence or analytic/arithmetic interpretation of that matrix is asserted. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct
namespace StrictEUnit
variable {k : Type*} [Field k]

def formalAmbientBaseAlgebra : Algebra (LaurentLogBase k) (RatFunc (LaurentSeries k)) :=
  (formalBaseEmbedding (k := k)).toRingHom.toAlgebra
/-- The scalar-tower proof is derived from the actual k-algebra hom. -/
def formalAmbientBaseTower := IsScalarTower.of_algHom (formalBaseEmbedding (k := k))

attribute [local instance 10] formalAmbientBaseAlgebra

@[simp] theorem formalAmbientBase_algebraMap (b : LaurentLogBase k) :
    algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)) b = formalBaseEmbedding b := rfl

variable [CharZero k] {n : Type*} [Fintype n] [DecidableEq n]
variable (N:ℕ) (hN:N≠0)
  (Y : Matrix n n (RatFunc (LaurentSeries k))) (A : Matrix n n (LaurentLogBase k))
  (hdet : Y.det ≠ 0)
  (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
    ∑ l, formalBaseEmbedding (A i l) * Y l j)
local instance formalMatrixGeneratedAddCommGroup :
    AddCommGroup (matrixGeneratedAlgebra (B := LaurentLogBase k) Y) :=
  @Ring.toAddCommGroup _ (matrixGeneratedAlgebra (B := LaurentLogBase k) Y).toRing

include hN hdet hy in
theorem formalCandidate_faithfullyFlat :
    Module.FaithfullyFlat (LaurentLogBase k) (matrixGeneratedAlgebra (B := LaurentLogBase k) Y) := by
  exact manuscript_matrixGeneratedAlgebra_faithfullyFlat N hN (formalAmbientDerivation N hN) Y A hdet
    (formalBaseEmbedding_differential N hN) hy

def formalCandidateMultiplicationEquiv :=
  manuscriptCandidateMultiplicationEquiv N hN (formalAmbientDerivation N hN) Y A hdet
    (formalBaseEmbedding_differential N hN) hy
    (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx)

def formalCandidateCoaction :=
  manuscriptCandidateCoaction N hN (formalAmbientDerivation N hN) Y A hdet
    (formalBaseEmbedding_differential N hN) hy
    (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx)

theorem formalCandidateCoaction_canonical_bijective :
    Function.Bijective (relativeCandidateCanonical (formalCandidateCoaction N hN Y A hdet hy)) :=
  manuscriptCandidateCoaction_canonical_bijective N hN (formalAmbientDerivation N hN) Y A hdet
    (formalBaseEmbedding_differential N hN) hy
    (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx)

theorem formalCandidateCoaction_differential
    (r : matrixGeneratedAlgebra (B := LaurentLogBase k) Y) :
    tensorDerivation (candidateKDerivation (B := LaurentLogBase k)
      (manuscriptBaseDerivation (k := k) N) (formalAmbientDerivation N hN) Y A
      (formalBaseEmbedding_differential N hN) hy)
      (formalCandidateCoaction N hN Y A hdet hy r) =
      formalCandidateCoaction N hN Y A hdet hy
        (candidateKDerivation (B := LaurentLogBase k)
          (manuscriptBaseDerivation (k := k) N) (formalAmbientDerivation N hN) Y A
          (formalBaseEmbedding_differential N hN) hy r) :=
  manuscriptCandidateCoaction_differential N hN (formalAmbientDerivation N hN) Y A hdet
    (formalBaseEmbedding_differential N hN) hy
    (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx) r

theorem formalCandidateCoaction_counit
    (r : matrixGeneratedAlgebra (B := LaurentLogBase k) Y) :
    candidateCounitEval (R := matrixGeneratedAlgebra (B := LaurentLogBase k) Y)
      (manuscriptBaseDerivation (k := k) N)
      (candidateKDerivation (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N)
        (formalAmbientDerivation N hN) Y A (formalBaseEmbedding_differential N hN) hy)
      (candidateKDerivation_base (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N)
        (formalAmbientDerivation N hN) Y A (formalBaseEmbedding_differential N hN) hy)
      (candidateKDerivation_constants (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N)
        (formalAmbientDerivation N hN) Y A (formalBaseEmbedding_differential N hN) hy
        (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx))
      (formalCandidateCoaction N hN Y A hdet hy r) = r :=
  manuscriptCandidateCoaction_counit N hN (formalAmbientDerivation N hN) Y A hdet
    (formalBaseEmbedding_differential N hN) hy
    (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx) r

#print axioms formalAmbientBaseAlgebra
#print axioms formalAmbientBaseTower
#print axioms formalAmbientBase_algebraMap
#print axioms formalCandidate_faithfullyFlat
#print axioms formalCandidateMultiplicationEquiv
#print axioms formalCandidateCoaction
#print axioms formalCandidateCoaction_canonical_bijective
#print axioms formalCandidateCoaction_differential
#print axioms formalCandidateCoaction_counit
end StrictEUnit
