import V5ActualKummerLift136
import V5ActualNaturalRelative135
import V5SubalgebraKummerFinish140
import V5ActualExplicitFinish140
import V5ActualSameKummerEuler136
import V5ActualMixedMarkAliases136
import V5ActualOrdinaryMixed136
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 1000000
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
include hf hA
/-- Finish the actual reciprocal lift with the operator and its rule supplied
inside the abstract cover construction before actual specialization. -/
theorem v5ActualKummerExponential140
    (q : ℕ) (hq : 0 < q) (α : v5ActualCover125 A →ₐ[AlgebraicComplex] V5LaurentBase)
    (hbase : α.toRingHom.comp (algebraMap V5LaurentBase (v5ActualCover125 A)) =
      v5LaurentPower q)
    (hm : ∀ t : v5ActualCover125 A,
      v5LaurentMark135 AlgebraicComplex (α t) =
        v5WideFieldCandidatePoint A (t : V5WideFieldCandidate A))
    (i j : Fin r) (hij : (f i).val 1 * (f j).val 1 = 1) :
    ∃ a b : AlgebraicComplex, a ≠ 0 ∧ (f i).val 1 = (a : ℂ) * Complex.exp (b : ℂ) := by
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
  letI : CommRing (v5ActualCover125 A) := (v5ActualCover125 A).toCommRing
  letI : AddCommGroup (v5ActualCover125 A) := (v5ActualCover125 A).toCommRing.toAddCommGroup
  letI : AddCommMonoid (v5ActualCover125 A) := (v5ActualCover125 A).toCommRing.toAddCommMonoid
  let assembly := v5ActualNaturalRelative135 A
  let eRel := Classical.choose assembly.2
  let heRel := Classical.choose_spec assembly.2
  let uC := v5WideMixedConstantUnit f A hf hA i j hij
  let u0 := v5AmbientConstantUnit136
    (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (S := v5WideSolutionAlgebra f)
    (v5WideActualMixedDerivation104 f A hA) uC
  let hu0 := v5ActualOwnOrdinaryMixedConstant136 f A hA uC.val
  let forward := v5SubalgebraKummerFinish140
    (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (H := V5WideOwnConstants A)
    (W := v5WideSolutionAlgebra f) (L := V5LaurentBase) (C := ℂ)
    (v5WideOwnCoaction A) (v5GenericOwnIdentity123 A)
    v5LaurentBaseDerivation (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)
    (v5WideOwnCoaction_differential A) (v5WideSolutionDerivation f A hA)
    (v5WideSolution_base_compatible f A hA)
    (LaurentPolynomial.T 1) q v5LaurentEulerDerivation127 (v5LaurentPower q) α hbase
    (v5ActualSameKummerEuler136 A q α hbase)
    eRel heRel assembly.1
    (v5LaurentMark135 AlgebraicComplex) (v5WideFieldCandidatePoint A) hm
    (v5WideSolutionEvaluation f) (v5ActualMixedMarkBaseCompatibility136 f A hf hA)
    u0 ((f i).val 1) ((f j).val 1) hu0
    (Q := fun a _ => ∃ α β : AlgebraicComplex, α ≠ 0 ∧ a = (α : ℂ) * Complex.exp (β : ℂ))
    (by
      intro algBL tower hpower hB D hD hde
      exact v5ActualExplicitAddFinish140 f hf A hA q hq hpower hB D hD
        ((f i).val 1) ((f j).val 1) hde)
  exact forward (v5ActualKummerLift136 f A hf hA α hm i j hij)
end StrictEUnit
#print axioms StrictEUnit.v5ActualKummerExponential140
