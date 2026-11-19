import V5MixedConstantsDescent

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k C M H : Type*} [Field k] [CommRing C] [CommRing M] [CommRing H]
  [Algebra k C] [Algebra k M] [Algebra k H]

def v5_horizontalCounit (ε : H →ₐ[k] k) : C ⊗[k] H →ₐ[k] C :=
  (Algebra.TensorProduct.rid k k C).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k C) ε)

theorem v5_horizontalCounit_natural (i : C →ₐ[k] M) (ε : H →ₐ[k] k)
    (z : C ⊗[k] H) :
    i (v5_horizontalCounit ε z) =
      v5_horizontalCounit ε (Algebra.TensorProduct.map i (AlgHom.id k H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c h =>
    change i (ε h • c) = ε h • i c
    exact i.toLinearMap.map_smul _ _

/-- An injective compatible square reflects the counit law. -/
theorem v5_horizontalCounit_of_square
    (i : C →ₐ[k] M) (hi : Function.Injective i)
    (δ : C →ₐ[k] C ⊗[k] H) (q : M →ₐ[k] M ⊗[k] H)
    (hsquare : ∀ c, Algebra.TensorProduct.map i (AlgHom.id k H) (δ c) = q (i c))
    (ε : H →ₐ[k] k) (hε : ∀ m, v5_horizontalCounit ε (q m) = m) (c : C) :
    v5_horizontalCounit ε (δ c) = c := by
  apply hi
  rw [v5_horizontalCounit_natural, hsquare, hε]

variable {R : Type*} [CommRing R] [Nontrivial R] [Algebra k R]

def v5_horizontalInclusion (e : R ⊗[k] C ≃ₐ[k] M) : C →ₐ[k] M :=
  e.toAlgHom.comp Algebra.TensorProduct.includeRight

theorem v5_horizontalInclusion_injective (e : R ⊗[k] C ≃ₐ[k] M) :
    Function.Injective (v5_horizontalInclusion e) :=
  e.injective.comp (Algebra.TensorProduct.includeRight_injective
    (RingHom.injective (algebraMap k R)))

theorem v5_horizontalInclusion_tensor (e : R ⊗[k] C ≃ₐ[k] M) (z : C ⊗[k] H) :
    Algebra.TensorProduct.map (v5_horizontalInclusion e) (AlgHom.id k H) z =
    Algebra.TensorProduct.map e.toAlgHom (AlgHom.id k H)
      ((Algebra.TensorProduct.assoc k R C H).symm ((1 : R) ⊗ₜ[k] z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul c h => rfl

/-- The actual differential descent construction inherits the mixed counit.
Only the law on M is supplied; no counit law on the horizontal factor is assumed. -/
theorem v5_mixedHorizontalMap_counit
    (d : Derivation k R R) (dM : Derivation k M M)
    (hc : ∀ r : R, d r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] M)
    (he : ∀ x, dM (e x) = e (tensorDerivation d x))
    (q : M →ₐ[k] M ⊗[k] H)
    (hq : ∀ x, tensorDerivation dM (q x) = q (dM x))
    (ε : H →ₐ[k] k) (hε : ∀ m, v5_horizontalCounit ε (q m) = m) (c : C) :
    v5_horizontalCounit ε (v5_mixedHorizontalMap d dM hc e he q hq c) = c := by
  apply v5_horizontalCounit_of_square (v5_horizontalInclusion e)
    (v5_horizontalInclusion_injective e) _ q _ ε hε c
  intro c
  rw [v5_horizontalInclusion_tensor, v5_mixedHorizontalMap_square]
  rfl

end StrictEUnit
#print axioms StrictEUnit.v5_horizontalCounit_of_square
#print axioms StrictEUnit.v5_mixedHorizontalMap_counit
