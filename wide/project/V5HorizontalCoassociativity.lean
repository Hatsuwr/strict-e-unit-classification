import V5HorizontalCounit

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k C M H : Type*} [Field k] [CommRing C] [CommRing M] [CommRing H]
  [Algebra k C] [Algebra k M] [Algebra k H]

theorem v5_horizontalAssoc_natural (i : C →ₐ[k] M) (z : (C ⊗[k] H) ⊗[k] H) :
    Algebra.TensorProduct.map i (AlgHom.id k (H ⊗[k] H))
      (Algebra.TensorProduct.assoc k C H H z) =
    Algebra.TensorProduct.assoc k M H H
      (Algebra.TensorProduct.map (Algebra.TensorProduct.map i (AlgHom.id k H))
        (AlgHom.id k H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x h =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul c g => rfl

theorem v5_horizontalCoassoc_left (i : C →ₐ[k] M)
    (δ : C →ₐ[k] C ⊗[k] H) (q : M →ₐ[k] M ⊗[k] H)
    (hsquare : ∀ c, Algebra.TensorProduct.map i (AlgHom.id k H) (δ c) = q (i c))
    (z : C ⊗[k] H) :
    Algebra.TensorProduct.map i (AlgHom.id k (H ⊗[k] H))
      (Algebra.TensorProduct.assoc k C H H
        (Algebra.TensorProduct.map δ (AlgHom.id k H) z)) =
    Algebra.TensorProduct.assoc k M H H
      (Algebra.TensorProduct.map q (AlgHom.id k H)
        (Algebra.TensorProduct.map i (AlgHom.id k H) z)) := by
  rw [v5_horizontalAssoc_natural]
  congr 1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c h => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hsquare]

theorem v5_horizontalCoassoc_right (i : C →ₐ[k] M)
    (Δ : H →ₐ[k] H ⊗[k] H) (z : C ⊗[k] H) :
    Algebra.TensorProduct.map i (AlgHom.id k (H ⊗[k] H))
      (Algebra.TensorProduct.map (AlgHom.id k C) Δ z) =
    Algebra.TensorProduct.map (AlgHom.id k M) Δ
      (Algebra.TensorProduct.map i (AlgHom.id k H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c h => rfl

theorem v5_horizontalTensor_injective {D : Type*} [CommRing D] [Algebra k D]
    (i : C →ₐ[k] M) (hi : Function.Injective i) :
    Function.Injective (Algebra.TensorProduct.map i (AlgHom.id k D)) := by
  letI : Module.Free k D := Module.Free.of_divisionRing k D
  letI : Module.Flat k D := Module.Flat.of_free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := D) i.toLinearMap hi

/-- Coassociativity descends along an injective compatible horizontal square. -/
theorem v5_horizontalCoassoc_of_square
    (i : C →ₐ[k] M) (hi : Function.Injective i)
    (δ : C →ₐ[k] C ⊗[k] H) (q : M →ₐ[k] M ⊗[k] H)
    (hsquare : ∀ c, Algebra.TensorProduct.map i (AlgHom.id k H) (δ c) = q (i c))
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hΔ : ∀ m, Algebra.TensorProduct.assoc k M H H
      (Algebra.TensorProduct.map q (AlgHom.id k H) (q m)) =
      Algebra.TensorProduct.map (AlgHom.id k M) Δ (q m)) (c : C) :
    Algebra.TensorProduct.assoc k C H H
      (Algebra.TensorProduct.map δ (AlgHom.id k H) (δ c)) =
    Algebra.TensorProduct.map (AlgHom.id k C) Δ (δ c) := by
  apply v5_horizontalTensor_injective i hi
  rw [v5_horizontalCoassoc_left i δ q hsquare, v5_horizontalCoassoc_right,
    hsquare, hΔ]

variable {R : Type*} [CommRing R] [Nontrivial R] [Algebra k R]

/-- The actual differential horizontal descent inherits coassociativity
from the law on the relative mixed algebra, not as an extra hypothesis on C. -/
theorem v5_mixedHorizontalMap_coassoc
    (d : Derivation k R R) (dM : Derivation k M M)
    (hc : ∀ r : R, d r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] M)
    (he : ∀ x, dM (e x) = e (tensorDerivation d x))
    (q : M →ₐ[k] M ⊗[k] H)
    (hq : ∀ x, tensorDerivation dM (q x) = q (dM x))
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hΔ : ∀ m, Algebra.TensorProduct.assoc k M H H
      (Algebra.TensorProduct.map q (AlgHom.id k H) (q m)) =
      Algebra.TensorProduct.map (AlgHom.id k M) Δ (q m)) (c : C) :
    let δ := v5_mixedHorizontalMap d dM hc e he q hq
    Algebra.TensorProduct.assoc k C H H
      (Algebra.TensorProduct.map δ (AlgHom.id k H) (δ c)) =
    Algebra.TensorProduct.map (AlgHom.id k C) Δ (δ c) := by
  apply v5_horizontalCoassoc_of_square (v5_horizontalInclusion e)
    (v5_horizontalInclusion_injective e) _ q _ Δ hΔ c
  intro c
  rw [v5_horizontalInclusion_tensor, v5_mixedHorizontalMap_square]
  rfl

end StrictEUnit
#print axioms StrictEUnit.v5_horizontalCoassoc_of_square
#print axioms StrictEUnit.v5_mixedHorizontalMap_coassoc
