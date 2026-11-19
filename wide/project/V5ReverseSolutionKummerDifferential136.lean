import V5ActualSolutionKummerDifferential136
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

def v5TransportDerivation136 {k U V : Type*} [CommRing k] [CommRing U] [CommRing V]
    [Algebra k U] [Algebra k V] (e : U ≃ₐ[k] V) (d : Derivation k U U) :
    Derivation k V V :=
  Derivation.mk' (e.toLinearMap.comp (d.toLinearMap.comp e.symm.toLinearMap)) (by
    intro x y
    change e (d (e.symm (x * y))) = _
    rw [map_mul, d.leibniz]
    simp only [map_add, map_smul, smul_eq_mul, map_mul, e.apply_symm_apply, LinearMap.comp_apply]
    all_goals rfl)

theorem v5TransportTensorDerivationRule136
    {k B U V : Type*} [CommRing k] [CommRing B] [CommRing U] [CommRing V]
    [Algebra B U] [Algebra B V]
    [Algebra k (U ⊗[B] V)] [Algebra k (V ⊗[B] U)]
    (e : U ⊗[B] V ≃ₐ[k] V ⊗[B] U)
    (he : ∀ u v, e (u ⊗ₜ[B] v) = v ⊗ₜ[B] u)
    (d : Derivation k (U ⊗[B] V) (U ⊗[B] V))
    (dU : U → U) (dV : V → V)
    (hd : ∀ u v, d (u ⊗ₜ[B] v) = dU u ⊗ₜ[B] v + u ⊗ₜ[B] dV v)
    (u : U) (v : V) :
    v5TransportDerivation136 e d (v ⊗ₜ[B] u) =
      dV v ⊗ₜ[B] u + v ⊗ₜ[B] dU u := by
  change e (d (e.symm (v ⊗ₜ[B] u))) = _
  have hi : e.symm (v ⊗ₜ[B] u) = u ⊗ₜ[B] v := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  rw [hi, hd, map_add, he, he]
  exact add_comm _ _

theorem v5LaurentPowerScalarTower136 {K : Type*} [Field K]
    [Algebra (LaurentPolynomial K) (LaurentPolynomial K)] (q : ℕ)
    (hpower : ∀ p, algebraMap (LaurentPolynomial K) (LaurentPolynomial K) p = v5LaurentPower q p) :
    IsScalarTower K (LaurentPolynomial K) (LaurentPolynomial K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [hpower]
  change LaurentPolynomial.C a = v5LaurentPower q (LaurentPolynomial.C a)
  simp only [v5LaurentPower, LaurentPolynomial.eval₂_C, RingHom.id_apply]

attribute [local instance 6000] solutionRing136 solutionAddGroup136 solutionAddMonoid136
  solutionCoefficientAlgebra136 solutionLaurentAlgebra136 solutionLaurentModule136
  solutionTensorCoefficientAlgebra136
local instance reverseAlgebraSMulComm136 (U V Z : Type*) [CommRing U] [CommRing V]
    [CommRing Z] [Algebra U Z] [Algebra V Z] : SMulCommClass U V Z :=
  ⟨fun u v z => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra) (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    [Algebra V5LaurentBase V5LaurentBase]
    (q : ℕ)
    (hpower : ∀ p, algebraMap V5LaurentBase V5LaurentBase p = v5LaurentPower q p)

local instance (priority := 6000) reversedSolutionCoefficientAlgebra136 :
    Algebra AlgebraicComplex (V5LaurentBase ⊗[V5LaurentBase] (v5WideSolutionAlgebra f)) :=
  @Algebra.TensorProduct.leftAlgebra V5LaurentBase AlgebraicComplex
    V5LaurentBase (v5WideSolutionAlgebra f) inferInstance inferInstance inferInstance
    (solutionRing136 f).toSemiring (solutionLaurentAlgebra136 f)
    inferInstance inferInstance
    (reverseAlgebraSMulComm136 V5LaurentBase AlgebraicComplex V5LaurentBase)

def v5ActualReversedSolutionKummerDifferential136 := by
  letI := v5LaurentPowerScalarTower136 q hpower
  let e := (Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f)
    V5LaurentBase).restrictScalars AlgebraicComplex
  exact v5TransportDerivation136 e (v5ActualSolutionKummerDifferential136 f A hA q hpower)

theorem v5ActualReversedSolutionKummerDifferential136_tmul
    (l : V5LaurentBase) (s : v5WideSolutionAlgebra f) :
    v5ActualReversedSolutionKummerDifferential136 f A hA q hpower (l ⊗ₜ[V5LaurentBase] s) =
      v5LaurentEulerLinear l ⊗ₜ[V5LaurentBase] s +
        l ⊗ₜ[V5LaurentBase] (q • v5ActualSolutionEuler f A hA s) := by
  letI := v5LaurentPowerScalarTower136 q hpower
  let e := (Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f)
    V5LaurentBase).restrictScalars AlgebraicComplex
  exact v5TransportTensorDerivationRule136 e (fun _ _ => rfl)
    (v5ActualSolutionKummerDifferential136 f A hA q hpower)
    (fun x => q • v5ActualSolutionEuler f A hA x) v5LaurentEulerLinear
    (v5ActualSolutionKummerDifferential136_tmul f A hA q hpower) s l

theorem v5ActualReversedSolutionKummerDifferential136_comm
    (x : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase) :
    v5ActualReversedSolutionKummerDifferential136 f A hA q hpower
      (Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f) V5LaurentBase x) =
    Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f) V5LaurentBase
      (v5ActualSolutionKummerDifferential136 f A hA q hpower x) := by
  letI := v5LaurentPowerScalarTower136 q hpower
  change Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f) V5LaurentBase
    (v5ActualSolutionKummerDifferential136 f A hA q hpower
    ((Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f) V5LaurentBase).symm
      (Algebra.TensorProduct.comm V5LaurentBase (v5WideSolutionAlgebra f) V5LaurentBase x))) = _
  rw [AlgEquiv.symm_apply_apply]
end StrictEUnit
#print axioms StrictEUnit.v5TransportDerivation136
#print axioms StrictEUnit.v5LaurentPowerScalarTower136
#print axioms StrictEUnit.v5ActualReversedSolutionKummerDifferential136
#print axioms StrictEUnit.v5ActualReversedSolutionKummerDifferential136_tmul
#print axioms StrictEUnit.v5ActualReversedSolutionKummerDifferential136_comm
