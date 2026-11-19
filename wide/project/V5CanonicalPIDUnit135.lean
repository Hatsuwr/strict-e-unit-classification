import V5ExplicitWeightUnit135
import V5FlatTorsionfree135
import V5OwnTorsorSquare
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B S H : Type*} [Field k] [CommRing B] [IsDomain B]
  [IsPrincipalIdealRing B] [Algebra k B]
  [CommRing S] [Nontrivial S] [Algebra B S] [Algebra k S]
  [IsScalarTower k B S] [Module.FaithfullyFlat B S]
  [CommRing H] [Algebra k H]
/-- PID unit descent directly from a natural coassociative own chart.
The target chart, both squares, and the target faithful flatness are derived. -/
theorem v5_pid_weight_unit_of_canonical_chart135
    (Δ : H →ₐ[k] H ⊗[k] H) (ε : H →ₐ[k] k)
    (hleft : ∀ h, v5ComponentLeftScalar ε (Δ h) = h)
    (ρ : S →ₐ[B] S ⊗[k] H)
    (e : S ⊗[B] S ≃ₐ[S] S ⊗[k] H)
    (he : ∀ a b, e (a ⊗ₜ[B] b) = a • ρ b)
    (hcoassoc : ∀ s, Algebra.TensorProduct.assoc k S H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ s)) =
      Algebra.TensorProduct.map (AlgHom.id S S) Δ (ρ s))
    (χ : Hˣ) (hχ : Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hε : ε (χ : H) = 1) :
    ∃ v : S, ρ v = v ⊗ₜ[k] (χ : H) ∧ IsUnit v := by
  letI : NoZeroSMulDivisors B S := v5_noZeroSMulDivisors_of_flat135
  let E := v5OwnTorsorTargetChartR (N := H) e
  have hid (z : S ⊗[k] H) :
      Algebra.TensorProduct.map (AlgHom.id S S) Δ z =
        Algebra.TensorProduct.map (AlgHom.id k S) Δ z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h => rfl
  have hρ (x : S ⊗[B] S) :
      E.toLinearEquiv (AlgebraTensorModule.lTensor S S ρ.toLinearMap x) =
        AlgebraTensorModule.lTensor S S Δ.toLinearMap (e x) := by
    exact v5OwnTorsorSquare (e.restrictScalars k) ρ ρ Δ he
      (fun s => (hcoassoc s).trans (hid (ρ s))) x
  have hassoc (z : S ⊗[k] H) :
      Algebra.TensorProduct.assoc k S H H (z ⊗ₜ[k] (χ : H)) =
        AlgebraTensorModule.lTensor S S ((TensorProduct.mk k H H).flip (χ : H)) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul a h => rfl
  have hw (x : S ⊗[B] S) :
      E.toLinearEquiv
        (AlgebraTensorModule.lTensor S S (v5WeightTensorMap (B := B) (χ : H)) x) =
      AlgebraTensorModule.lTensor S S ((TensorProduct.mk k H H).flip (χ : H)) (e x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      change v5OwnTorsorTargetChart (e.restrictScalars k)
        (a ⊗ₜ[B] (b ⊗ₜ[k] (χ : H))) = _
      rw [v5OwnTorsorTargetChart_tmul]
      exact hassoc (e (a ⊗ₜ[B] b))
  let er := e.toRingEquiv
  letI : Algebra S (S ⊗[k] H) := ρ.toRingHom.toAlgebra
  let F : S ⊗[B] S ≃ₐ[S] S ⊗[k] H :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm B S S).toRingEquiv.trans er)
      (by
        intro s
        change e ((1 : S) ⊗ₜ[B] s) = ρ s
        simpa only [he, one_smul])
  letI : Module.FaithfullyFlat S (S ⊗[k] H) :=
    Module.FaithfullyFlat.of_linearEquiv S (S ⊗[B] S) F.symm.toLinearEquiv
  exact v5_weight_unit_of_pid_explicit_chart135 (A := S) Δ ε hleft ρ.toLinearMap
    χ hχ hε e E.toLinearEquiv hρ hw
    (fun s => by
      change ρ s = e ((1 : S) ⊗ₜ[B] s)
      simpa only [he, one_smul])
end StrictEUnit
#print axioms StrictEUnit.v5_pid_weight_unit_of_canonical_chart135
