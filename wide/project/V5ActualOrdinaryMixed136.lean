import V5WideActualMixedScalars
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 5000] Subalgebra.algebra Subalgebra.algebra' Subalgebra.toCommRing
namespace StrictEUnit
/-- Renaming the own factor derivation does not change a balanced tensor
operator; compatibility proof choices are propositionally irrelevant. -/
theorem v5MixedRelativeDerivation_congr136
    {k B R W : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing W]
    [Algebra k B] [Algebra k R] [Algebra k W] [Algebra B R] [Algebra B W]
    [IsScalarTower k B R] [IsScalarTower k B W]
    (dB : Derivation k B B) (dR dR' : Derivation k R R) (dW : Derivation k W W)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hR' : ∀ b, dR' (algebraMap B R b) = algebraMap B R (dB b))
    (hW : ∀ b, dW (algebraMap B W b) = algebraMap B W (dB b))
    (h : dR = dR') :
    mixedRelativeTensorDerivation dB dR dW hR hW =
      mixedRelativeTensorDerivation dB dR' dW hR' hW := by
  subst dR'
  rfl
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
local instance (priority := 6000) ordinarySolutionRing136 : CommRing (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing
local instance (priority := 6000) ordinarySolutionAddGroup136 : AddCommGroup (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommGroup
local instance (priority := 6000) ordinarySolutionAddMonoid136 : AddCommMonoid (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommMonoid
local instance (priority := 6000) ordinarySolutionCoefficientAlgebra136 :
    Algebra AlgebraicComplex (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).algebra
local instance (priority := 6000) ordinarySolutionLaurentAlgebra136 :
    Algebra V5LaurentBase (v5WideSolutionAlgebra f) := v5WideSolutionLaurentAlgebra f
local instance (priority := 6000) ordinarySolutionLaurentModule136 :
    Module V5LaurentBase (v5WideSolutionAlgebra f) := Algebra.toModule
/-- The own-PV derivation and the candidate derivation are the same definition. -/
theorem v5ActualOwnOrdinaryDerivation136 :
    v5WideOwnDerivation A = v5WideFieldCandidateDerivation A := rfl

def v5ActualOwnOrdinaryMixedDerivation136 :=
  mixedRelativeTensorDerivation v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideSolutionDerivation f A hA)
    (v5WideOwnDerivation_base A) (v5WideSolution_base_compatible f A hA)

theorem v5ActualOwnOrdinaryMixedDerivation136_eq :
    v5ActualOwnOrdinaryMixedDerivation136 f A hA = v5WideActualMixedDerivation104 f A hA :=
  v5MixedRelativeDerivation_congr136 v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideFieldCandidateDerivation A)
    (v5WideSolutionDerivation f A hA) (v5WideOwnDerivation_base A)
    (v5WideFieldCandidate_base A) (v5WideSolution_base_compatible f A hA)
    (v5ActualOwnOrdinaryDerivation136 A)

theorem v5ActualOwnOrdinaryMixedConstant136 (z : V5WideActualMixedConstants104 f A hA) :
    v5ActualOwnOrdinaryMixedDerivation136 f A hA
      (z : V5WideFieldCandidate A ⊗[V5LaurentBase] v5WideSolutionAlgebra f) = 0 := by
  rw [v5ActualOwnOrdinaryMixedDerivation136_eq]
  exact z.property
end StrictEUnit
#print axioms StrictEUnit.v5MixedRelativeDerivation_congr136
#print axioms StrictEUnit.v5ActualOwnOrdinaryDerivation136
#print axioms StrictEUnit.v5ActualOwnOrdinaryMixedDerivation136_eq
#print axioms StrictEUnit.v5ActualOwnOrdinaryMixedConstant136
