import V5WeightUnitDescent
import V5ProductComponentInvariants
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
section Explicit
variable {k A H : Type*} [Field k] [CommRing A] [Algebra k A]
  [CommRing H] [Algebra k H]
def v5ExplicitComponentEval135 (ε : H →ₐ[k] k) : A ⊗[k] H →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (ε.toLinearMap.lTensor A)
@[simp] theorem v5ExplicitComponentEval135_tmul (ε : H →ₐ[k] k) (a : A) (h : H) :
    v5ExplicitComponentEval135 ε (a ⊗ₜ[k] h) = ε h • a := rfl

def v5ExplicitExtendedEigenline135 (Δ : H →ₐ[k] H ⊗[k] H) (χ : H) :
    Submodule A (A ⊗[k] H) :=
  LinearMap.eqLocus (AlgebraTensorModule.lTensor A A Δ.toLinearMap)
    (AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip χ))

theorem v5ExplicitExtendedWeight_iff135
    (Δ : H →ₐ[k] H ⊗[k] H) (ε : H →ₐ[k] k)
    (hleft : ∀ h, v5ComponentLeftScalar ε (Δ h) = h)
    (χ : H) (hχ : Δ χ = χ ⊗ₜ[k] χ) (x : A ⊗[k] H) :
    AlgebraTensorModule.lTensor A A Δ.toLinearMap x =
      AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip χ) x ↔
    ∃ a : A, x = a ⊗ₜ[k] χ := by
  let C := (v5ComponentLeftScalar ε).toLinearMap
  have hC (y : A ⊗[k] H) :
      AlgebraTensorModule.lTensor A A C (AlgebraTensorModule.lTensor A A Δ.toLinearMap y) = y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      change a ⊗ₜ[k] v5ComponentLeftScalar ε (Δ h) = _
      rw [hleft]
  have hW (y : A ⊗[k] H) :
      AlgebraTensorModule.lTensor A A C
        (AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip χ) y) =
      v5ExplicitComponentEval135 ε y ⊗ₜ[k] χ := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.add_tmul]
    | tmul a h =>
      change a ⊗ₜ[k] (algebraMap k H (ε h) * χ) = (ε h • a) ⊗ₜ[k] χ
      rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  constructor
  · intro hx
    refine ⟨v5ExplicitComponentEval135 ε x, ?_⟩
    have h := congrArg (AlgebraTensorModule.lTensor A A C) hx
    simpa only [hC, hW] using h
  · rintro ⟨a,rfl⟩
    change a ⊗ₜ[k] Δ χ = a ⊗ₜ[k] (χ ⊗ₜ[k] χ)
    rw [hχ]

def v5ExplicitExtendedLineEquiv135
    (Δ : H →ₐ[k] H ⊗[k] H) (ε : H →ₐ[k] k)
    (hleft : ∀ h, v5ComponentLeftScalar ε (Δ h) = h)
    (χ : H) (hχ : Δ χ = χ ⊗ₜ[k] χ) (hε : ε χ = 1) :
    v5ExplicitExtendedEigenline135 (A := A) Δ χ ≃ₗ[A] A := by
  let v : v5ExplicitExtendedEigenline135 (A := A) Δ χ :=
    ⟨1 ⊗ₜ[k] χ, (v5ExplicitExtendedWeight_iff135 Δ ε hleft χ hχ _).mpr ⟨1,rfl⟩⟩
  let f : A →ₗ[A] v5ExplicitExtendedEigenline135 (A := A) Δ χ :=
    LinearMap.toSpanSingleton A _ v
  have hf (a : A) : (f a).val = a ⊗ₜ[k] χ := by
    change a • ((1 : A) ⊗ₜ[k] χ) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  apply LinearEquiv.symm
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have he := congrArg (fun x : v5ExplicitExtendedEigenline135 (A := A) Δ χ =>
      v5ExplicitComponentEval135 ε x.val) hab
    simpa only [hf, v5ExplicitComponentEval135_tmul, hε, one_smul] using he
  · intro x
    obtain ⟨a,ha⟩ := (v5ExplicitExtendedWeight_iff135 Δ ε hleft χ hχ x.val).mp x.property
    exact ⟨a, Subtype.ext ((hf a).trans ha.symm)⟩
end Explicit
section Descent
variable {k B A S H : Type*} [Field k] [CommRing B] [IsDomain B]
  [IsPrincipalIdealRing B] [Algebra k B]
  [CommRing A] [Nontrivial A] [Algebra B A] [Algebra k A]
  [Module.FaithfullyFlat B A]
  [CommRing S] [Algebra B S] [Algebra k S] [IsScalarTower k B S]
  [NoZeroSMulDivisors B S]
  [CommRing H] [Algebra k H]
  [Algebra S (A ⊗[k] H)] [Module.FaithfullyFlat S (A ⊗[k] H)]

/-- Given actual equivariant charts on a faithfully flat cover, the weighted
line contains an ambient unit. The global generator is derived over the PID. -/
theorem v5_weight_unit_of_pid_explicit_chart135
    (Δ : H →ₐ[k] H ⊗[k] H) (ε : H →ₐ[k] k)
    (hleft : ∀ h, v5ComponentLeftScalar ε (Δ h) = h)
    (ρ : S →ₗ[B] S ⊗[k] H) (χ : Hˣ)
    (hχ : Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hε : ε (χ : H) = 1)
    (e : A ⊗[B] S ≃ₐ[A] A ⊗[k] H)
    (E : A ⊗[B] (S ⊗[k] H) ≃ₗ[A] A ⊗[k] (H ⊗[k] H))
    (hρ : ∀ x, E (AlgebraTensorModule.lTensor A A ρ x) =
      AlgebraTensorModule.lTensor A A Δ.toLinearMap (e x))
    (hw : ∀ x, E (AlgebraTensorModule.lTensor A A (v5WeightTensorMap (B := B) (χ : H)) x) =
      AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip (χ : H)) (e x))
    (hbase : ∀ s : S, algebraMap S (A ⊗[k] H) s = e ((1 : A) ⊗ₜ[B] s)) :
    ∃ v : S, ρ v = v ⊗ₜ[k] (χ : H) ∧ IsUnit v := by
  let M := v5WeightSpace ρ (χ : H)
  let transport := v5LinearEqualizerTransport e.toLinearEquiv E
    (AlgebraTensorModule.lTensor A A ρ)
    (AlgebraTensorModule.lTensor A A (v5WeightTensorMap (B := B) (χ : H)))
    (AlgebraTensorModule.lTensor A A Δ.toLinearMap)
    (AlgebraTensorModule.lTensor A A ((TensorProduct.mk k H H).flip (χ : H))) hρ hw
  let localLine : A ⊗[B] M ≃ₗ[A] v5ExplicitExtendedEigenline135 (A := A) Δ (χ : H) :=
    (v5WeightSpaceBaseChange (A := A) ρ (χ : H)).trans transport
  let eA : A ⊗[B] M ≃ₗ[A] A := localLine.trans (v5ExplicitExtendedLineEquiv135 (A := A) Δ ε hleft (χ : H) hχ hε)
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
    let y : v5ExplicitExtendedEigenline135 (A := A) Δ (χ : H) :=
      ⟨1 ⊗ₜ[k] (χ : H), (v5ExplicitExtendedWeight_iff135 Δ ε hleft (χ : H) hχ _).mpr ⟨1, rfl⟩⟩
    refine ⟨localLine.symm y, ?_⟩
    have he : Ψ (localLine.symm y) = (y : A ⊗[k] H) := by
      rw [← hlocal, localLine.apply_symm_apply]
    rw [he]
    exact χ.isUnit.map (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H)
  obtain ⟨b, hb⟩ := v5_pid_line_unit_generator_of_faithfullyFlat eA M.subtype Ψ hΨ hunit
  exact ⟨(b 1 : S), (b 1).property, hb⟩
end Descent
end StrictEUnit
#print axioms StrictEUnit.v5ExplicitExtendedWeight_iff135
#print axioms StrictEUnit.v5ExplicitExtendedLineEquiv135
#print axioms StrictEUnit.v5_weight_unit_of_pid_explicit_chart135
