import V5MixedRelativeCoaction
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k L S W N : Type*}
  [CommRing k] [CommRing L] [CommRing S] [CommRing W] [CommRing N]
  [Algebra k L] [Algebra k S] [Algebra L S] [IsScalarTower k L S]
  [Algebra k W] [Algebra L W] [IsScalarTower k L W] [Algebra k N]
/-- The own candidate includes into its mixed tensor algebra. -/
def v5OwnMixedInclusion135 : S →ₐ[k] S ⊗[L] W :=
  Algebra.TensorProduct.includeLeft
/-- Extend the own inclusion on the varying coefficient factor. -/
def v5OwnMixedTensorMap135 : S ⊗[k] N →ₐ[k] (S ⊗[L] W) ⊗[k] N :=
  Algebra.TensorProduct.map v5OwnMixedInclusion135 (AlgHom.id k N)
theorem v5OwnMixedShuffle135 (z : S ⊗[k] N) :
    v5MixedCoactionShuffle ((1 : W) ⊗ₜ[L] z) =
      v5OwnMixedTensorMap135 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s n => rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
/-- Own coaction and mixed coaction commute with the own inclusion. -/
theorem v5OwnMixedCoaction135 (ρ : S →ₐ[L] S ⊗[k] N) (s : S) :
    v5MixedRelativeCoaction (k := k) (B := L) (S := W) ρ (v5OwnMixedInclusion135 (k := k) s) =
      v5OwnMixedTensorMap135 (ρ s) := by
  change v5MixedCoactionShuffle ((1 : W) ⊗ₜ[L] ρ s) = _
  exact v5OwnMixedShuffle135 (ρ s)
/-- The include-left trivial maps commute with the same tensor map. -/
theorem v5OwnMixedTrivial135 (s : S) :
    (Algebra.TensorProduct.includeLeft : S ⊗[L] W →ₐ[k] (S ⊗[L] W) ⊗[k] N)
      (v5OwnMixedInclusion135 (k := k) s) =
    v5OwnMixedTensorMap135
      ((Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] N) s) := rfl
end StrictEUnit
#print axioms StrictEUnit.v5OwnMixedInclusion135
#print axioms StrictEUnit.v5OwnMixedTensorMap135
#print axioms StrictEUnit.v5OwnMixedShuffle135
#print axioms StrictEUnit.v5OwnMixedCoaction135
#print axioms StrictEUnit.v5OwnMixedTrivial135
