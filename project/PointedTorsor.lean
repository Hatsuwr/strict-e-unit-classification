import CanonicalTorsor
import NumericalCharacter

/-! A point of a canonical-map torsor gives a genuine algebra chart.
The point and canonical bijectivity are inputs; the chart is derived. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
section General
variable {k S H : Type*} [CommRing k] [CommRing S] [CommRing H]
  [Algebra k S] [Algebra k H]

/-- Evaluation on the first tensor factor at an actual algebraic point. -/
def pointTensorEval (p : S →ₐ[k] k) (M : Type*) [CommRing M] [Algebra k M] :
    S ⊗[k] M →ₐ[k] M :=
  (Algebra.TensorProduct.lid k M).toAlgHom.comp
    (Algebra.TensorProduct.map p (AlgHom.id k M))

@[simp] theorem pointTensorEval_tmul (p : S →ₐ[k] k)
    (M : Type*) [CommRing M] [Algebra k M] (s : S) (m : M) :
    pointTensorEval p M (s ⊗ₜ[k] m) = p s • m := rfl

/-- Orbit chart associated to the point. -/
def pointedOrbitMap (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k) :
    S →ₐ[k] H := (pointTensorEval p H).comp ρ

/-- The candidate inverse comes from the actual inverse canonical map. -/
def pointedOrbitInverse (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (hcan : Function.Bijective (torsorCanonical ρ)) : H →ₐ[k] S :=
  (pointTensorEval p S).comp
    (((torsorCanonicalEquiv ρ hcan).symm.toAlgHom.restrictScalars k).comp
      (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H))

theorem point_eval_canonical (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (z : S ⊗[k] S) :
    pointedOrbitMap ρ p (pointTensorEval p S z) =
      pointTensorEval p H (torsorCanonical ρ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    rw [pointTensorEval_tmul, map_smul, torsorCanonical_tmul, map_mul,
      pointTensorEval_tmul]
    simp only [Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pointedOrbitMap_inverse (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (hcan : Function.Bijective (torsorCanonical ρ)) (h : H) :
    pointedOrbitMap ρ p (pointedOrbitInverse ρ p hcan h) = h := by
  change pointedOrbitMap ρ p
    (pointTensorEval p S ((torsorCanonicalEquiv ρ hcan).symm (1 ⊗ₜ[k] h))) = h
  rw [point_eval_canonical]
  change pointTensorEval p H
    ((torsorCanonicalEquiv ρ hcan) ((torsorCanonicalEquiv ρ hcan).symm _)) = h
  simp

theorem point_eval_canonical_inverse (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (hcan : Function.Bijective (torsorCanonical ρ)) (z : S ⊗[k] H) :
    pointedOrbitInverse ρ p hcan (pointTensorEval p H z) =
      pointTensorEval p S ((torsorCanonicalEquiv ρ hcan).symm z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r h =>
    rw [pointTensorEval_tmul, map_smul]
    have ht : r ⊗ₜ[k] h = r • ((1 : S) ⊗ₜ[k] h) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul]
    rw [show r • (torsorCanonicalEquiv ρ hcan).symm (1 ⊗ₜ[k] h) =
      (r ⊗ₜ[k] (1 : S)) * (torsorCanonicalEquiv ρ hcan).symm (1 ⊗ₜ[k] h) from
      Algebra.smul_def r _]
    rw [map_mul, pointTensorEval_tmul]
    simp only [Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pointedOrbitInverse_map (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (hcan : Function.Bijective (torsorCanonical ρ)) (s : S) :
    pointedOrbitInverse ρ p hcan (pointedOrbitMap ρ p s) = s := by
  change pointedOrbitInverse ρ p hcan (pointTensorEval p H (ρ s)) = s
  rw [point_eval_canonical_inverse]
  have hc : (torsorCanonicalEquiv ρ hcan) ((1 : S) ⊗ₜ[k] s) = ρ s := by
    rw [torsorCanonicalEquiv_tmul, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← hc, AlgEquiv.symm_apply_apply, pointTensorEval_tmul, map_one, one_smul]

/-- The point produces a genuine chart, with no chart hypothesis. -/
def pointedTorsorEquiv (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (hcan : Function.Bijective (torsorCanonical ρ)) : S ≃ₐ[k] H :=
  AlgEquiv.ofAlgHom (pointedOrbitMap ρ p) (pointedOrbitInverse ρ p hcan)
    (AlgHom.ext (pointedOrbitMap_inverse ρ p hcan))
    (AlgHom.ext (pointedOrbitInverse_map ρ p hcan))

theorem pointTensorEval_assoc (p : S →ₐ[k] k) (z : S ⊗[k] H) (h : H) :
    pointTensorEval p (H ⊗[k] H)
      (Algebra.TensorProduct.assoc k S H H (z ⊗ₜ[k] h)) =
    pointTensorEval p H z ⊗ₜ[k] h := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    simp only [Algebra.TensorProduct.assoc_tmul, pointTensorEval_tmul, smul_tmul']
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]

theorem point_eval_twice_coaction (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (z : S ⊗[k] H) :
    pointTensorEval p (H ⊗[k] H)
      (Algebra.TensorProduct.assoc k S H H
        (Algebra.TensorProduct.map ρ (AlgHom.id k H) z)) =
    Algebra.TensorProduct.map (pointedOrbitMap ρ p) (AlgHom.id k H) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s h =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, pointTensorEval_assoc]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end General

section Coaction
variable {k S H : Type*} [CommRing k] [CommRing S] [CommRing H]
  [Algebra k S] [Bialgebra k H]

theorem point_eval_comul (p : S →ₐ[k] k) (z : S ⊗[k] H) :
    pointTensorEval p (H ⊗[k] H)
      (weightBaseChangeAlgHom S (Bialgebra.comulAlgHom k H) z) =
    Coalgebra.comul (R := k) (pointTensorEval p H z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s h =>
    simp only [weightBaseChangeAlgHom_tmul, pointTensorEval_tmul,
      Bialgebra.comulAlgHom_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The derived chart is equivariant by the original coassociativity law. -/
theorem pointedTorsorEquiv_coaction
    (ρ : S →ₐ[k] S ⊗[k] H) (p : S →ₐ[k] k)
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : S,
      Algebra.TensorProduct.assoc k S H H
        (Algebra.TensorProduct.map ρ (AlgHom.id k H) (ρ s)) =
      weightBaseChangeAlgHom S (Bialgebra.comulAlgHom k H) (ρ s))
    (s : S) :
    numericalTensorChart (pointedTorsorEquiv ρ p hcan) (ρ s) =
      Coalgebra.comul (R := k) (pointedTorsorEquiv ρ p hcan s) := by
  have hh := congrArg (pointTensorEval p (H ⊗[k] H)) (hcoassoc s)
  rw [point_eval_twice_coaction, point_eval_comul] at hh
  exact hh
end Coaction
end StrictEUnit

#print axioms StrictEUnit.pointTensorEval
#print axioms StrictEUnit.pointTensorEval_tmul
#print axioms StrictEUnit.pointedOrbitMap
#print axioms StrictEUnit.pointedOrbitInverse
#print axioms StrictEUnit.point_eval_canonical
#print axioms StrictEUnit.pointedOrbitMap_inverse
#print axioms StrictEUnit.point_eval_canonical_inverse
#print axioms StrictEUnit.pointedOrbitInverse_map
#print axioms StrictEUnit.pointedTorsorEquiv
#print axioms StrictEUnit.pointTensorEval_assoc
#print axioms StrictEUnit.point_eval_twice_coaction
#print axioms StrictEUnit.point_eval_comul
#print axioms StrictEUnit.pointedTorsorEquiv_coaction

