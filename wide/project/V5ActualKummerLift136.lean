import V5HopfKummerMarked136
import V5AmbientConstantUnit136
import V5ActualConstantAmbient136
import V5ActualMixedMark136
import V5ActualKummerData135
import V5LaurentMark135
import LaurentLogBase
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 5000] Subalgebra.algebra Subalgebra.algebra' Subalgebra.toCommRing
namespace StrictEUnit
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
def v5ActualKummerLift136
    (α : v5ActualCover126 A →ₐ[AlgebraicComplex] LaurentPolynomial AlgebraicComplex)
    (hm : ∀ t : v5ActualCover126 A,
      v5LaurentMark135 AlgebraicComplex (α t) =
        v5WideFieldCandidatePoint A (t : V5WideFieldCandidate A))
    (i j : Fin r) (hij : (f i).val 1 * (f j).val 1 = 1) := by
  letI : CommRing (V5WideFieldCandidate A) := (V5WideFieldCandidate A).toCommRing
  letI : AddCommGroup (V5WideFieldCandidate A) := (V5WideFieldCandidate A).toCommRing.toAddCommGroup
  letI : AddCommMonoid (V5WideFieldCandidate A) := (V5WideFieldCandidate A).toCommRing.toAddCommMonoid
  letI : Algebra AlgebraicComplex (V5WideFieldCandidate A) :=
    ((V5WideFieldCandidate A).restrictScalars AlgebraicComplex).algebra
  letI : Algebra V5LaurentBase (V5WideFieldCandidate A) := (V5WideFieldCandidate A).algebra
  letI : Module V5LaurentBase (V5WideFieldCandidate A) := Algebra.toModule
  letI : CommRing (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).toCommRing
  letI : AddCommGroup (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).toCommRing.toAddCommGroup
  letI : AddCommMonoid (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).toCommRing.toAddCommMonoid
  letI : Algebra AlgebraicComplex (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).algebra
  letI : Algebra V5LaurentBase (v5WideSolutionAlgebra f) := v5WideSolutionLaurentAlgebra f
  letI : Module V5LaurentBase (v5WideSolutionAlgebra f) := Algebra.toModule
  letI := v5WideOwnHopfAlgebra A
  letI : Algebra.FiniteType AlgebraicComplex (V5WideOwnConstants A) :=
    v5WideOwnConstants_finiteType A
  letI := v5WideOwnConstants_isReduced A
  letI := v5WideOwnCandidate_faithfullyFlat A
  let spec := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).1
  let uniq := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).2
  let uC := v5WideMixedConstantUnit f A hf hA i j hij
  let u0 := v5AmbientConstantUnit136
    (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (S := v5WideSolutionAlgebra f)
    (v5WideActualMixedDerivation104 f A hA) uC
  let lift := v5HopfKummerMarked136
    (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (H := V5WideOwnConstants A)
    (L := LaurentPolynomial AlgebraicComplex) (W := v5WideSolutionAlgebra f) (C := ℂ)
    (v5WideOwnMultiplicationEquiv A) (v5WideOwnCoaction A)
    (by intro a b; exact v5_ownChart_tmul_smul (v5WideOwnMultiplicationEquiv A) a b)
    (v5WideOwnCoaction_coassoc A)
    (v5WideOwnAntipode A) rfl (v5GenericOwnIdentity123 A) spec.1 spec.2
    (fun P hP hPε => uniq P ⟨hP, hPε⟩) α
    (v5LaurentMark135 AlgebraicComplex) (v5WideFieldCandidatePoint A) hm
    (v5WideSolutionEvaluation f) (v5ActualMixedTensorMark136 f A hf hA)
    (v5ActualMixedTensorMark136_tmul f A hf hA) u0 ((f i).val 1) ((f j).val 1)
    (v5ActualMixedTensorMark136_unit_value f A hf hA i j hij)
    (v5ActualMixedTensorMark136_unit_inverse_value f A hf hA i j hij)
  exact lift (v5ActualConstantAmbientReciprocal136 f A hf hA i j hij)
end StrictEUnit
#print axioms StrictEUnit.v5ActualKummerLift136
