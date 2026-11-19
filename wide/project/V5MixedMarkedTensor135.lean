import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k L S W C : Type*}
  [CommRing k] [CommRing L] [CommRing S] [CommRing W] [CommRing C]
  [Algebra k L] [Algebra k S] [Algebra L S] [IsScalarTower k L S]
  [Algebra k W] [Algebra L W] [Algebra k C]
/-- An algebraic own mark and a possibly nonalgebraic mixed coefficient mark
induce a mark on the mixed tensor product when their base marks agree. -/
def v5MixedMarkedTensor135
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l)) :
    S ⊗[L] W →ₐ[k] C := by
  letI : Algebra L C := (pW.toRingHom.comp (algebraMap L W)).toAlgebra
  let pSL : S →ₐ[L] C :=
    { (algebraMap k C).comp pS.toRingHom with commutes' := hm }
  let pWL : W →ₐ[L] C :=
    { pW.toRingHom with commutes' := fun _ => rfl }
  let f := Algebra.TensorProduct.lift pSL pWL (fun _ _ => Commute.all _ _)
  refine { f.toRingHom with commutes' := ?_ }
  intro a
  change algebraMap k C (pS (algebraMap k S a)) * pW (1 : W) = algebraMap k C a
  rw [pS.commutes, map_one, mul_one]
  rfl
@[simp] theorem v5MixedMarkedTensor135_tmul
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l))
    (s : S) (w : W) :
    v5MixedMarkedTensor135 pS pW hm (s ⊗ₜ[L] w) =
      algebraMap k C (pS s) * pW w := rfl
@[simp] theorem v5MixedMarkedTensor135_includeLeft
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l))
    (s : S) :
    v5MixedMarkedTensor135 pS pW hm
      ((Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[L] W) s) =
      algebraMap k C (pS s) := by
  change algebraMap k C (pS s) * pW (1 : W) = _
  rw [map_one, mul_one]
@[simp] theorem v5MixedMarkedTensor135_includeRight
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l))
    (w : W) :
    v5MixedMarkedTensor135 pS pW hm
      ((Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) w) = pW w := by
  change algebraMap k C (pS (1 : S)) * pW w = _
  rw [map_one, map_one, one_mul]
theorem v5MixedMarkedTensor135_comp_includeLeft
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l)) :
    (v5MixedMarkedTensor135 pS pW hm).comp
      (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[L] W) =
      (Algebra.ofId k C).comp pS := by
  ext s
  exact v5MixedMarkedTensor135_includeLeft pS pW hm s
theorem v5MixedMarkedTensor135_comp_includeRight
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l))
    [IsScalarTower k L W] :
    (v5MixedMarkedTensor135 pS pW hm).comp
      ((Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W).restrictScalars k) = pW := by
  ext w
  exact v5MixedMarkedTensor135_includeRight pS pW hm w
end StrictEUnit
#print axioms StrictEUnit.v5MixedMarkedTensor135
#print axioms StrictEUnit.v5MixedMarkedTensor135_tmul
#print axioms StrictEUnit.v5MixedMarkedTensor135_includeLeft
#print axioms StrictEUnit.v5MixedMarkedTensor135_includeRight

#print axioms StrictEUnit.v5MixedMarkedTensor135_comp_includeLeft
#print axioms StrictEUnit.v5MixedMarkedTensor135_comp_includeRight
