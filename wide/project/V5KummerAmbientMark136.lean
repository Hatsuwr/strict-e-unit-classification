import V5KummerMarks136
import V5KummerAmbientMap136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B T L R W C : Type*}
  [Field k] [CommRing B] [CommRing T] [CommRing L] [CommRing R] [CommRing W] [CommRing C]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W] [Algebra k C]
  [Algebra B T] [Algebra T L] [Algebra T R] [Algebra B L] [Algebra B R] [Algebra B W]
  [IsScalarTower B T L] [IsScalarTower B T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R]
theorem v5KummerAmbientMark136
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k) (pW : W →ₐ[k] C)
    (hT : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (hR : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b))
    (z : R ⊗[B] W) :
    v5MixedMarkedTensor135 (v5MarkedBaseChangePoint135 pL pR hT)
      (v5MixedMarkedTensor135 pL pW hB)
      (v5KummerTensorMarksCompatible136 pL pR pW hT hB)
      (v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) z) =
      v5MixedMarkedTensor135 pR pW hR z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r w =>
    simp only [v5KummerAmbientMap136_tmul, v5MixedMarkedTensor135_tmul,
      v5MarkedBaseChangePoint135_tmul, map_one, one_mul]
end StrictEUnit
#print axioms StrictEUnit.v5KummerAmbientMark136
