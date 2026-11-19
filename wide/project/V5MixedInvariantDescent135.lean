import V5FaithfulTensorEqualizer135
import V5MixedRelativeCoaction
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k L S W N : Type*} [Field k] [CommRing L] [CommRing S] [CommRing W] [CommRing N]
  [Algebra k L] [Algebra k S] [Algebra k W] [Algebra k N]
  [Algebra L S] [Algebra L W] [IsScalarTower k L S] [IsScalarTower k L W]
/-- The canonical natural chart converts the mixed action into tensor descent. -/
def v5MixedDescentChart135 (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N) :
    S ⊗[L] (S ⊗[L] W) ≃ₐ[k] (S ⊗[L] W) ⊗[k] N :=
  ((Algebra.TensorProduct.assoc L S S W).symm.restrictScalars k).trans
    (((Algebra.TensorProduct.comm L (S ⊗[L] S) W).restrictScalars k).trans
      (((Algebra.TensorProduct.congr (AlgEquiv.refl : W ≃ₐ[L] W)
        (e.restrictScalars L)).restrictScalars k).trans
        (v5MixedCoactionShuffle (k := k) (B := L) (R := S) (S := W) (H := N))))

@[simp] theorem v5MixedDescentChart135_tmul
    (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N) (a b : S) (w : W) :
    v5MixedDescentChart135 (W := W) e (a ⊗ₜ[L] (b ⊗ₜ[L] w)) =
      v5MixedCoactionShuffle (w ⊗ₜ[L] e (a ⊗ₜ[L] b)) := by
  simp only [v5MixedDescentChart135, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.assoc_symm_tmul, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

/-- Every mixed invariant descends exactly to the coefficient algebra.
There is no quotient bialgebra, reducedness, domain, or coefficient-flatness hypothesis. -/
theorem v5_mixed_invariants_descend135 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N)
    (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (x : S ⊗[L] W)
    (hx : v5MixedRelativeCoaction ρ x =
      (Algebra.TensorProduct.includeLeft : S ⊗[L] W →ₐ[k] (S ⊗[L] W) ⊗[k] N) x) :
    ∃ w : W, (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) w = x := by
  let F := v5MixedDescentChart135 (W := W) e
  have h0 (y : S ⊗[L] W) :
      F ((Algebra.TensorProduct.includeRight : S ⊗[L] W →ₐ[L] S ⊗[L] (S ⊗[L] W)) y) =
        v5MixedRelativeCoaction ρ y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul s w =>
      change v5MixedDescentChart135 e ((1 : S) ⊗ₜ[L] (s ⊗ₜ[L] w)) = _
      rw [v5MixedDescentChart135_tmul, he, one_smul]
      rfl
  have h1 (y : S ⊗[L] W) :
      F (Algebra.TensorProduct.map (AlgHom.id L S)
        (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) y) =
      (Algebra.TensorProduct.includeLeft : S ⊗[L] W →ₐ[k] (S ⊗[L] W) ⊗[k] N) y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul s w =>
      change v5MixedDescentChart135 e (s ⊗ₜ[L] ((1 : S) ⊗ₜ[L] w)) = _
      rw [v5MixedDescentChart135_tmul]
      have hunit : e (s ⊗ₜ[L] (1 : S)) = s ⊗ₜ[k] (1 : N) := e.commutes s
      rw [hunit, v5MixedCoactionShuffle_tmul]
      rfl
  apply v5_faithful_tensor_equalizer135 x
  apply F.injective
  rw [h0, h1, hx]
theorem v5_mixed_fixed_iff135 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N)
    (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (x : S ⊗[L] W) :
    v5MixedRelativeCoaction ρ x =
      (Algebra.TensorProduct.includeLeft : S ⊗[L] W →ₐ[k] (S ⊗[L] W) ⊗[k] N) x ↔
    ∃ w : W, (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) w = x := by
  constructor
  · exact v5_mixed_invariants_descend135 ρ e he x
  · rintro ⟨w,rfl⟩
    change v5MixedRelativeCoaction ρ ((1 : S) ⊗ₜ[L] w) =
      ((1 : S) ⊗ₜ[L] w) ⊗ₜ[k] (1 : N)
    rw [v5MixedRelativeCoaction_tmul, map_one]
    exact v5MixedCoactionShuffle_tmul w (1 : S) (1 : N)

theorem v5_mixed_exact_invariant_image135 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N)
    (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b) :
    Function.Injective (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) ∧
      ∀ x : S ⊗[L] W,
        v5MixedRelativeCoaction ρ x =
          (Algebra.TensorProduct.includeLeft : S ⊗[L] W →ₐ[k] (S ⊗[L] W) ⊗[k] N) x →
        ∃ w : W, (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) w = x :=
  ⟨v5_faithful_includeRight_injective135, v5_mixed_invariants_descend135 ρ e he⟩
end StrictEUnit
#print axioms StrictEUnit.v5MixedDescentChart135
#print axioms StrictEUnit.v5MixedDescentChart135_tmul
#print axioms StrictEUnit.v5_mixed_invariants_descend135
#print axioms StrictEUnit.v5_mixed_fixed_iff135
#print axioms StrictEUnit.v5_mixed_exact_invariant_image135
