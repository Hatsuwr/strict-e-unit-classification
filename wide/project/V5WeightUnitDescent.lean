import V5ExtendedRegularEigenline
import V5WeightedBaseChange
import V5PIDLineDescent

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit

/-- Explicit rank-one equivalence of the scalar-extended regular eigenline. -/
def v5ExtendedRegularLineEquiv {k A H : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [CommRing H] [Bialgebra k H]
    (χ : H) (hχ : Coalgebra.comul (R := k) χ = χ ⊗ₜ[k] χ)
    (hε : Coalgebra.counit (R := k) χ = 1) :
    v5ExtendedRegularEigenline (k := k) (R := A) χ ≃ₗ[A] A := by
  let v : v5ExtendedRegularEigenline (k := k) (R := A) χ :=
    ⟨1 ⊗ₜ[k] χ, (v5ExtendedRegular_weight_iff χ hχ _).mpr ⟨1, rfl⟩⟩
  let f : A →ₗ[A] v5ExtendedRegularEigenline (k := k) (R := A) χ :=
    LinearMap.toSpanSingleton A _ v
  have hf (a : A) : (f a).val = a ⊗ₜ[k] χ := by
    change a • ((1 : A) ⊗ₜ[k] χ) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  apply LinearEquiv.symm
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have he := congrArg (fun x : v5ExtendedRegularEigenline (k := k) (R := A) χ =>
      v5ComponentEval x.val) hab
    simpa only [hf, v5ComponentEval_tmul, hε, one_smul] using he
  · intro x
    obtain ⟨a, ha⟩ := (v5ExtendedRegular_weight_iff χ hχ x.val).mp x.property
    exact ⟨a, Subtype.ext ((hf a).trans ha.symm)⟩

section Descent
variable {k B A S H : Type*} [Field k] [CommRing B] [IsDomain B]
  [IsPrincipalIdealRing B] [Algebra k B]
  [CommRing A] [Nontrivial A] [Algebra B A] [Algebra k A]
  [Module.FaithfullyFlat B A]
  [CommRing S] [Algebra B S] [Algebra k S] [IsScalarTower k B S]
  [NoZeroSMulDivisors B S]
  [CommRing H] [Bialgebra k H]
  [Algebra S (A ⊗[k] H)] [Module.FaithfullyFlat S (A ⊗[k] H)]

/-- Given actual equivariant charts on a faithfully flat cover, the weighted
line contains an ambient unit. The global generator is derived over the PID. -/
theorem v5_weight_unit_of_pid_regular_chart
    (ρ : S →ₗ[B] S ⊗[k] H) (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hε : Coalgebra.counit (R := k) (χ : H) = 1)
    (e : A ⊗[B] S ≃ₐ[A] A ⊗[k] H)
    (E : A ⊗[B] (S ⊗[k] H) ≃ₗ[A] A ⊗[k] (H ⊗[k] H))
    (hρ : ∀ x, E (AlgebraTensorModule.lTensor A A ρ x) =
      AlgebraTensorModule.lTensor A A (Coalgebra.comul (R := k) (A := H)) (e x))
    (hw : ∀ x, E (AlgebraTensorModule.lTensor A A (v5WeightTensorMap (B := B) (χ : H)) x) =
      AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip (χ : H)) (e x))
    (hbase : ∀ s : S, algebraMap S (A ⊗[k] H) s = e ((1 : A) ⊗ₜ[B] s)) :
    ∃ v : S, ρ v = v ⊗ₜ[k] (χ : H) ∧ IsUnit v := by
  let M := v5WeightSpace ρ (χ : H)
  let transport := v5LinearEqualizerTransport e.toLinearEquiv E
    (AlgebraTensorModule.lTensor A A ρ)
    (AlgebraTensorModule.lTensor A A (v5WeightTensorMap (B := B) (χ : H)))
    (AlgebraTensorModule.lTensor A A (Coalgebra.comul (R := k) (A := H)))
    (AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip (χ : H))) hρ hw
  let localLine : A ⊗[B] M ≃ₗ[A] v5ExtendedRegularEigenline (k := k) (R := A) (χ : H) :=
    (v5WeightSpaceBaseChange (A := A) ρ (χ : H)).trans transport
  let eA : A ⊗[B] M ≃ₗ[A] A := localLine.trans (v5ExtendedRegularLineEquiv (k := k) (A := A) (χ : H) hχ hε)
  let Ψ : A ⊗[B] M →ₗ[A] A ⊗[k] H :=
    e.toLinearMap.comp (AlgebraTensorModule.lTensor A A M.subtype)
  have hΨ : ∀ a m, Ψ (a ⊗ₜ[B] m) =
      algebraMap A (A ⊗[k] H) a * algebraMap S (A ⊗[k] H) (M.subtype m) := by
    intro a m
    change e (a ⊗ₜ[B] (m : S)) = _
    rw [hbase, ← Algebra.smul_def, ← map_smul]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have hlocal (x : A ⊗[B] M) : (localLine x).val = Ψ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul a m => rfl
  have hunit : ∃ x : A ⊗[B] M, IsUnit (Ψ x) := by
    let y : v5ExtendedRegularEigenline (k := k) (R := A) (χ : H) :=
      ⟨1 ⊗ₜ[k] (χ : H), (v5ExtendedRegular_weight_iff (χ : H) hχ _).mpr ⟨1, rfl⟩⟩
    refine ⟨localLine.symm y, ?_⟩
    have he : Ψ (localLine.symm y) = (y : A ⊗[k] H) := by
      rw [← hlocal, localLine.apply_symm_apply]
    rw [he]
    exact χ.isUnit.map (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H)
  obtain ⟨b, hb⟩ := v5_pid_line_unit_generator_of_faithfullyFlat eA M.subtype Ψ hΨ hunit
  exact ⟨(b 1 : S), (b 1).property, hb⟩
end Descent
end StrictEUnit
#print axioms StrictEUnit.v5ExtendedRegularLineEquiv
#print axioms StrictEUnit.v5_weight_unit_of_pid_regular_chart
