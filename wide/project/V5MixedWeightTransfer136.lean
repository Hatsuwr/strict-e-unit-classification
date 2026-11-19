import V5MixedRelativeCoaction
import V5MixedConstantsDescent
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
section Restrict
variable {k B R S H N : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing S] [CommRing H] [CommRing N]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k H] [Algebra k N]
theorem v5MixedShuffleRestriction136 (q : H →ₐ[k] N) (s : S) (z : R ⊗[k] H) :
    v5MixedCoactionShuffle (s ⊗ₜ[B] Algebra.TensorProduct.map (AlgHom.id B R) q z) =
      Algebra.TensorProduct.map (AlgHom.id k (R ⊗[B] S)) q
        (v5MixedCoactionShuffle (s ⊗ₜ[B] z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r h => rfl
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
/-- Restricting the own constant factor commutes with the mixed coaction. -/
theorem v5MixedCoactionRestriction136 (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N)
    (x : R ⊗[B] S) :
    v5MixedRelativeCoaction ((Algebra.TensorProduct.map (AlgHom.id B R) q).comp ρ) x =
      Algebra.TensorProduct.map (AlgHom.id k (R ⊗[B] S)) q (v5MixedRelativeCoaction ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s => exact v5MixedShuffleRestriction136 q s (ρ r)
  | add x y hx hy => simp only [map_add, hx, hy]
end Restrict
section Square
variable {k R C M H N : Type*} [CommRing k] [CommRing R] [CommRing C]
  [CommRing M] [CommRing H] [CommRing N]
  [Algebra k R] [Algebra k C] [Algebra k M] [Algebra k H] [Algebra k N]
theorem v5MixedSquareRestriction136
    (e : R ⊗[k] C ≃ₐ[k] M) (q : H →ₐ[k] N) (z : C ⊗[k] H) :
    Algebra.TensorProduct.map (AlgHom.id k M) q
      (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id k H)
        ((Algebra.TensorProduct.assoc k R C H).symm ((1 : R) ⊗ₜ[k] z))) =
      Algebra.TensorProduct.map e.toAlgHom (AlgHom.id k N)
        ((Algebra.TensorProduct.assoc k R C N).symm
          ((1 : R) ⊗ₜ[k] Algebra.TensorProduct.map (AlgHom.id k C) q z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c h => rfl
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
/-- A checked comparison square transfers a quotient weight to the ambient algebra. -/
theorem v5MixedSquareWeight136
    (e : R ⊗[k] C ≃ₐ[k] M) (δ : C →ₐ[k] C ⊗[k] H)
    (ρ : M →ₐ[k] M ⊗[k] H)
    (hsquare : ∀ c, Algebra.TensorProduct.map e.toAlgHom (AlgHom.id k H)
      ((Algebra.TensorProduct.assoc k R C H).symm ((1 : R) ⊗ₜ[k] δ c)) =
      ρ (e ((1 : R) ⊗ₜ[k] c)))
    (q : H →ₐ[k] N) (c : C) (χ : N)
    (hw : Algebra.TensorProduct.map (AlgHom.id k C) q (δ c) = c ⊗ₜ[k] χ) :
    Algebra.TensorProduct.map (AlgHom.id k M) q (ρ (e ((1 : R) ⊗ₜ[k] c))) =
      e ((1 : R) ⊗ₜ[k] c) ⊗ₜ[k] χ := by
  rw [← hsquare, v5MixedSquareRestriction136, hw]
  rfl
end Square
section Horizontal
variable {k B R S C H N : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [CommRing S] [CommRing C] [CommRing H] [CommRing N]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [Algebra k C] [Algebra k H] [Algebra k N]
/-- The existing horizontal comparison square supplies the ambient weight;
restriction of the own action is performed before mixed base change. -/
theorem v5MixedHorizontalOwnWeight136
    (dR : Derivation k R R) (dM : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (hc : ∀ r : R, dR r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] R ⊗[B] S)
    (he : ∀ x, dM (e x) = e (tensorDerivation dR x))
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hρ : ∀ x, tensorDerivation dM (v5MixedRelativeCoaction ρ x) =
      v5MixedRelativeCoaction ρ (dM x))
    (q : H →ₐ[k] N) (c : C) (χ : N)
    (hw : Algebra.TensorProduct.map (AlgHom.id k C) q
      (v5_mixedHorizontalMap dR dM hc e he (v5MixedRelativeCoaction ρ) hρ c) =
      c ⊗ₜ[k] χ) :
    v5MixedRelativeCoaction ((Algebra.TensorProduct.map (AlgHom.id B R) q).comp ρ)
      (e ((1 : R) ⊗ₜ[k] c)) = e ((1 : R) ⊗ₜ[k] c) ⊗ₜ[k] χ := by
  rw [v5MixedCoactionRestriction136]
  exact v5MixedSquareWeight136 e _ _
    (v5_mixedHorizontalMap_square dR dM hc e he (v5MixedRelativeCoaction ρ) hρ) q c χ hw
end Horizontal
end StrictEUnit
#print axioms StrictEUnit.v5MixedShuffleRestriction136
#print axioms StrictEUnit.v5MixedCoactionRestriction136
#print axioms StrictEUnit.v5MixedSquareRestriction136
#print axioms StrictEUnit.v5MixedSquareWeight136
#print axioms StrictEUnit.v5MixedHorizontalOwnWeight136
