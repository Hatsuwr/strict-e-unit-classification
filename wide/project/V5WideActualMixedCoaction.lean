import V5WideActualMixedScalars
import V5MixedRelativeCoassoc
import V5MixedRelativeCounit
import V5HorizontalCoassociativity

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 120000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing

namespace StrictEUnit

section CounitAgreement

variable {k R H : Type*} [Field k] [CommRing R] [CommRing H] [Algebra k R] [Algebra k H]

private theorem v5_horizontalCounit_eq_tensorCounit (ε : H →ₐ[k] k) (z : R ⊗[k] H) :
    v5_horizontalCounit ε z = v5TensorCounitEval ε z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r h => simp [v5_horizontalCounit]

end CounitAgreement

variable {r : ℕ}
    (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

def v5WideMixedAction :=
  v5_mixedHorizontalMap (k := AlgebraicComplex) (R := V5WideFieldCandidate A)
    (C := V5WideActualMixedConstants104 f A hA) (H := V5WideOwnConstants A)
    (v5WideFieldCandidateDerivation A)
    (v5WideActualMixedDerivation104 f A hA) (v5WideOwnDerivation_constants A)
    (v5WideActualMixedComparisonK f A hA)
    (v5WideActualMixedComparisonK_differential f A hA)
    (v5WideActualRelativeMixedMap104 f A)
    (v5WideActualRelativeMixedMap104_differential f A hA)

def v5WideMixedActionCounit :=
  candidateCounit v5LaurentBaseDerivation (v5WideOwnDerivation A)
    (v5WideOwnDerivation_base A) (v5WideOwnDerivation_constants A)

theorem v5WideMixedAction_counit (c : V5WideActualMixedConstants104 f A hA) :
    v5_horizontalCounit (v5WideMixedActionCounit A) (v5WideMixedAction f A hA c) = c := by
  apply v5_mixedHorizontalMap_counit
  intro x
  rw [v5_horizontalCounit_eq_tensorCounit]
  exact v5MixedRelativeCoaction_counit (v5WideOwnCoaction A)
    (v5WideMixedActionCounit A) (v5WideOwnCoaction_counit A) x

theorem v5WideMixedAction_coassoc (c : V5WideActualMixedConstants104 f A hA) :
    Algebra.TensorProduct.assoc AlgebraicComplex (V5WideActualMixedConstants104 f A hA)
      (V5WideOwnConstants A) (V5WideOwnConstants A)
      (Algebra.TensorProduct.map (v5WideMixedAction f A hA)
        (AlgHom.id AlgebraicComplex (V5WideOwnConstants A)) (v5WideMixedAction f A hA c)) =
    Algebra.TensorProduct.map (AlgHom.id AlgebraicComplex (V5WideActualMixedConstants104 f A hA))
      (v5WideOwnComultiplication A) (v5WideMixedAction f A hA c) := by
  apply v5_mixedHorizontalMap_coassoc
  exact v5MixedRelativeCoaction_coassoc (v5WideOwnCoaction A)
    (v5WideOwnComultiplication A) (v5WideOwnCoaction_coassoc A)

end StrictEUnit
#print axioms StrictEUnit.v5WideMixedAction
#print axioms StrictEUnit.v5WideMixedActionCounit
#print axioms StrictEUnit.v5WideMixedAction_counit
#print axioms StrictEUnit.v5WideMixedAction_coassoc
