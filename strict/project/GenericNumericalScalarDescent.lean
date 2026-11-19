import FormalBaseChangedScalarUnitLift
import ArithmeticRecovery
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
/-- Numerical scalar descent with an abstract coefficient field and target ring.
The image-in-subfield condition is used only for the resulting scalar factor. -/
theorem numericalUnits_of_genericScalarUnitLift
    (k₀ : Subfield ℂ) {k C T L : Type*} [Field k]
    [CommRing C] [CommRing T] [CommRing L]
    [Algebra k C] [Algebra k T] [Algebra k L]
    (τ : L →+* ℂ) (hmem : ∀ a : k, τ (algebraMap k L a) ∈ k₀)
    (η : C →ₐ[k] L) (ξ : T →ₐ[k] L) (ι : C →ₐ[k] T)
    (hcompat : ∀ r : C, ξ (ι r) = η r)
    (hclass : ∀ v : Cˣ, HasExponentialForm k₀ (τ (η (v : C))))
    (hlift : ∀ u : Tˣ, ∃ v : Cˣ, ∃ a : kˣ,
      u = Units.map (algebraMap k T).toMonoidHom a * Units.map ι.toMonoidHom v)
    (u : Tˣ) : HasExponentialForm k₀ (τ (ξ (u : T))) := by
  obtain ⟨v, a, hu⟩ := hlift u
  have h := congrArg (fun w : Tˣ => τ (ξ (w : T))) hu
  change τ (ξ (u : T)) = τ (ξ (algebraMap k T (a : k) * ι (v : C))) at h
  rw [map_mul, ξ.commutes, hcompat, map_mul] at h
  rw [h]
  apply exponential_form_mul k₀ _ (hclass v)
  refine ⟨τ (algebraMap k L (a : k)), hmem _, ?_, 0, k₀.zero_mem, ?_⟩
  · exact (a.isUnit.map (τ.comp (algebraMap k L))).ne_zero
  · simp only [Complex.exp_zero, mul_one]

variable {k L : Type*} [Field k] [CommRing L] [Algebra k L]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))
local notation "Cand" => matrixGeneratedAlgebra (B:=LaurentLogBase k) Y
/-- Compose the numerical maps while both carrier structures are abstract. -/
def formalCandidate_genericNumericalCore
    (k₀ : Subfield ℂ) (τ : L →+* ℂ)
    (hmem : ∀ a : k, τ (algebraMap k L a) ∈ k₀)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] L)
    (ξ : (k ⊗[LaurentLogBase k] Cand) →ₐ[k] L) :=
  numericalUnits_of_genericScalarUnitLift (k:=k) (C:=Cand)
    (T:=k ⊗[LaurentLogBase k] Cand) (L:=L) k₀ τ hmem
    (formalMatrixCandidateEvaluation F Z ν) ξ
    (algebraicFiberSpecialization (k:=k) (B:=LaurentLogBase k) (R:=Cand))
end StrictEUnit
#print axioms StrictEUnit.numericalUnits_of_genericScalarUnitLift
#print axioms StrictEUnit.formalCandidate_genericNumericalCore
