import V5MarkedBaseChangePoint135
import V5MixedMarkedTensor135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B T L R W C : Type*}
  [Field k] [CommRing B] [CommRing T] [CommRing L] [CommRing R] [CommRing W] [CommRing C]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W] [Algebra k C]
  [Algebra B T] [Algebra T L] [Algebra T R] [Algebra B L] [Algebra B R] [Algebra B W]
  [IsScalarTower B T L] [IsScalarTower B T R]
  [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R]
theorem v5KummerBaseMarks136
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k) (pW : W →ₐ[k] C)
    (hT : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (hR : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b)) :
    ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b) := by
  intro b
  rw [IsScalarTower.algebraMap_apply B T L]
  rw [hT]
  rw [← IsScalarTower.algebraMap_apply B T R]
  exact hR b

theorem v5KummerTensorMarksCompatible136
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k) (pW : W →ₐ[k] C)
    (hT : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b)) :
    ∀ l, algebraMap k C
      (v5MarkedBaseChangePoint135 pL pR hT (algebraMap L (L ⊗[T] R) l)) =
      v5MixedMarkedTensor135 pL pW hB (algebraMap L (L ⊗[B] W) l) := by
  intro l
  change algebraMap k C (v5MarkedBaseChangePoint135 pL pR hT (l ⊗ₜ[T] (1 : R))) =
    v5MixedMarkedTensor135 pL pW hB (l ⊗ₜ[B] (1 : W))
  simp only [v5MarkedBaseChangePoint135_tmul, v5MixedMarkedTensor135_tmul, map_one, mul_one]
end StrictEUnit
#print axioms StrictEUnit.v5KummerBaseMarks136
#print axioms StrictEUnit.v5KummerTensorMarksCompatible136
