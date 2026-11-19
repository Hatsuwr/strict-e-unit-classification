import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k T L R : Type*} [Field k] [CommRing T] [CommRing L] [CommRing R]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra T L] [Algebra T R]
  [IsScalarTower k T L] [IsScalarTower k T R]
/-- Compatible algebraic marks induce a mark on their tensor base change. -/
def v5MarkedBaseChangePoint135
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t)) :
    L ⊗[T] R →ₐ[k] k := by
  letI : Algebra T k := (pL.toRingHom.comp (algebraMap T L)).toAlgebra
  let pLT : L →ₐ[T] k :=
    { pL.toRingHom with commutes' := fun _ => rfl }
  let pRT : R →ₐ[T] k :=
    { pR.toRingHom with commutes' := fun t => (hm t).symm }
  let f := Algebra.TensorProduct.lift pLT pRT (fun _ _ => Commute.all _ _)
  refine { f.toRingHom with commutes' := ?_ }
  intro a
  change pL (algebraMap k L a) * pR (1 : R) = algebraMap k k a
  rw [pL.commutes, map_one, mul_one]

@[simp] theorem v5MarkedBaseChangePoint135_tmul
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (l : L) (r : R) :
    v5MarkedBaseChangePoint135 pL pR hm (l ⊗ₜ[T] r) = pL l * pR r := rfl

@[simp] theorem v5MarkedBaseChangePoint135_includeLeft
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (l : L) :
    v5MarkedBaseChangePoint135 pL pR hm
      ((Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[T] R) l) = pL l := by
  change v5MarkedBaseChangePoint135 pL pR hm (l ⊗ₜ[T] (1 : R)) = _
  rw [v5MarkedBaseChangePoint135_tmul, map_one, mul_one]

@[simp] theorem v5MarkedBaseChangePoint135_includeRight
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (r : R) :
    v5MarkedBaseChangePoint135 pL pR hm
      ((Algebra.TensorProduct.includeRight : R →ₐ[T] L ⊗[T] R) r) = pR r := by
  change v5MarkedBaseChangePoint135 pL pR hm ((1 : L) ⊗ₜ[T] r) = _
  rw [v5MarkedBaseChangePoint135_tmul, map_one, one_mul]

theorem v5MarkedBaseChangePoint135_comp_includeLeft
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t)) :
    (v5MarkedBaseChangePoint135 pL pR hm).comp
      (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[T] R) = pL := by
  ext l
  exact v5MarkedBaseChangePoint135_includeLeft pL pR hm l

theorem v5MarkedBaseChangePoint135_comp_includeRight
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t)) :
    (v5MarkedBaseChangePoint135 pL pR hm).comp
      ((Algebra.TensorProduct.includeRight : R →ₐ[T] L ⊗[T] R).restrictScalars k) = pR := by
  ext r
  exact v5MarkedBaseChangePoint135_includeRight pL pR hm r
end StrictEUnit
#print axioms StrictEUnit.v5MarkedBaseChangePoint135
#print axioms StrictEUnit.v5MarkedBaseChangePoint135_tmul
#print axioms StrictEUnit.v5MarkedBaseChangePoint135_includeLeft
#print axioms StrictEUnit.v5MarkedBaseChangePoint135_includeRight
#print axioms StrictEUnit.v5MarkedBaseChangePoint135_comp_includeLeft
#print axioms StrictEUnit.v5MarkedBaseChangePoint135_comp_includeRight
