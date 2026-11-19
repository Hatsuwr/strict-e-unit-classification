import TensorConstants
import Mathlib.LinearAlgebra.TensorProduct.Associator

open scoped TensorProduct
open TensorProduct

noncomputable section
namespace StrictEUnit

variable {k R D C H : Type*} [Field k] [CommRing R] [CommRing D]
  [CommRing C] [CommRing H] [Algebra k R] [Algebra k D] [Algebra k C] [Algebra k H]

/-- Descend a map whose image is horizontal for differentiation on the
first factor. Exact constants make the descended map multiplicative. -/
def v5_descentOfHorizontalMap [Nontrivial R]
    (d : Derivation k R R)
    (hc : ∀ r : R, d r = 0 → ∃ c : k, algebraMap k R c = r)
    (F : C →ₐ[k] R ⊗[k] D) (hF : ∀ c, tensorDerivation d (F c) = 0) :
    C →ₐ[k] D :=
  (tensorConstantsEquiv d hc).symm.toAlgHom.comp
    (F.codRestrict (derivationConstants (tensorDerivation d)) hF)

theorem v5_descentOfHorizontalMap_spec [Nontrivial R]
    (d : Derivation k R R)
    (hc : ∀ r : R, d r = 0 → ∃ c : k, algebraMap k R c = r)
    (F : C →ₐ[k] R ⊗[k] D) (hF : ∀ c, tensorDerivation d (F c) = 0)
    (c : C) :
    (1 : R) ⊗ₜ[k] v5_descentOfHorizontalMap d hc F hF c = F c := by
  let w : derivationConstants (tensorDerivation (H := D) d) := ⟨F c, hF c⟩
  exact congrArg Subtype.val ((tensorConstantsEquiv d hc).apply_symm_apply w)

theorem v5_descentOfHorizontalMap_unique [Nontrivial R]
    (d : Derivation k R R)
    (hc : ∀ r : R, d r = 0 → ∃ c : k, algebraMap k R c = r)
    (F : C →ₐ[k] R ⊗[k] D) (hF : ∀ c, tensorDerivation d (F c) = 0)
    (g : C →ₐ[k] D) (hg : ∀ c, (1 : R) ⊗ₜ[k] g c = F c) :
    g = v5_descentOfHorizontalMap d hc F hF := by
  ext c
  apply Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k R))
  change (1 : R) ⊗ₜ[k] g c = (1 : R) ⊗ₜ[k] v5_descentOfHorizontalMap d hc F hF c
  rw [hg, v5_descentOfHorizontalMap_spec]

variable {M : Type*} [CommRing M] [Algebra k M]

/-- Move the differential to the leftmost factor under reassociation. -/
theorem v5_tensorDerivation_assoc
    (d : Derivation k R R) (x : (R ⊗[k] C) ⊗[k] H) :
    tensorDerivation d ((Algebra.TensorProduct.assoc k R C H) x) =
      (Algebra.TensorProduct.assoc k R C H) (tensorDerivation (tensorDerivation d) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x h =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul r c =>
      simp only [Algebra.TensorProduct.assoc_tmul, tensorDerivation_tmul]

/-- Differential compatibility is stable under tensoring with the identity. -/
theorem v5_tensorDerivation_map_right
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (dA : Derivation k A A) (dB : Derivation k B B)
    (e : A →ₐ[k] B) (he : ∀ a, dB (e a) = e (dA a))
    (x : A ⊗[k] H) :
    tensorDerivation dB (Algebra.TensorProduct.map e (AlgHom.id k H) x) =
      Algebra.TensorProduct.map e (AlgHom.id k H) (tensorDerivation dA x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h => simp only [Algebra.TensorProduct.map_tmul, tensorDerivation_tmul, he]

/-- Pull the mixed map through the horizontal comparison and reassociate.
The resulting map on C takes values in the actual horizontal kernel. -/
def v5_mixedChartPullback (e : R ⊗[k] C ≃ₐ[k] M)
    (q : M →ₐ[k] M ⊗[k] H) : C →ₐ[k] R ⊗[k] (C ⊗[k] H) :=
  (Algebra.TensorProduct.assoc k R C H).toAlgHom.comp
    ((Algebra.TensorProduct.map e.symm.toAlgHom (AlgHom.id k H)).comp
      (q.comp (e.toAlgHom.comp Algebra.TensorProduct.includeRight)))

theorem v5_mixedChartPullback_horizontal
    (d : Derivation k R R) (dM : Derivation k M M)
    (e : R ⊗[k] C ≃ₐ[k] M)
    (he : ∀ x, dM (e x) = e (tensorDerivation d x))
    (q : M →ₐ[k] M ⊗[k] H)
    (hq : ∀ x, tensorDerivation dM (q x) = q (dM x))
    (c : C) :
    tensorDerivation d (v5_mixedChartPullback e q c) = 0 := by
  have hinv (x : M) : tensorDerivation d (e.symm x) = e.symm (dM x) := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, ← he, AlgEquiv.apply_symm_apply]
  change tensorDerivation d ((Algebra.TensorProduct.assoc k R C H)
    (Algebra.TensorProduct.map e.symm.toAlgHom (AlgHom.id k H) (q (e ((1 : R) ⊗ₜ[k] c))))) = 0
  rw [v5_tensorDerivation_assoc,
    v5_tensorDerivation_map_right dM (tensorDerivation d) e.symm.toAlgHom hinv,
    hq, he, tensorDerivation_tmul, Derivation.map_one_eq_zero, zero_tmul]
  simp

/-- The mixed map obtained from exact constants and the comparison chart. -/
def v5_mixedHorizontalMap [Nontrivial R]
    (d : Derivation k R R) (dM : Derivation k M M)
    (hc : ∀ r : R, d r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] M)
    (he : ∀ x, dM (e x) = e (tensorDerivation d x))
    (q : M →ₐ[k] M ⊗[k] H)
    (hq : ∀ x, tensorDerivation dM (q x) = q (dM x)) : C →ₐ[k] C ⊗[k] H :=
  v5_descentOfHorizontalMap d hc (v5_mixedChartPullback e q)
    (v5_mixedChartPullback_horizontal d dM e he q hq)

theorem v5_mixedHorizontalMap_spec [Nontrivial R]
    (d : Derivation k R R) (dM : Derivation k M M)
    (hc : ∀ r : R, d r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] M)
    (he : ∀ x, dM (e x) = e (tensorDerivation d x))
    (q : M →ₐ[k] M ⊗[k] H)
    (hq : ∀ x, tensorDerivation dM (q x) = q (dM x)) (c : C) :
    (1 : R) ⊗ₜ[k] v5_mixedHorizontalMap d dM hc e he q hq c =
      v5_mixedChartPullback e q c :=
  v5_descentOfHorizontalMap_spec _ _ _ _ _


/-- The descended map recovers the original mixed map on the constant
factor, in the original tensor coordinates. -/
theorem v5_mixedHorizontalMap_square [Nontrivial R]
    (d : Derivation k R R) (dM : Derivation k M M)
    (hc : ∀ r : R, d r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] M)
    (he : ∀ x, dM (e x) = e (tensorDerivation d x))
    (q : M →ₐ[k] M ⊗[k] H)
    (hq : ∀ x, tensorDerivation dM (q x) = q (dM x)) (c : C) :
    Algebra.TensorProduct.map e.toAlgHom (AlgHom.id k H)
      ((Algebra.TensorProduct.assoc k R C H).symm
        ((1 : R) ⊗ₜ[k] v5_mixedHorizontalMap d dM hc e he q hq c)) =
        q (e ((1 : R) ⊗ₜ[k] c)) := by
  rw [v5_mixedHorizontalMap_spec]
  let E := Algebra.TensorProduct.congr e (AlgEquiv.refl (R := k) (A₁ := H))
  change E ((Algebra.TensorProduct.assoc k R C H).symm
    ((Algebra.TensorProduct.assoc k R C H)
      (E.symm (q (e ((1 : R) ⊗ₜ[k] c)))))) = _
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]


end StrictEUnit

#print axioms StrictEUnit.v5_descentOfHorizontalMap
#print axioms StrictEUnit.v5_descentOfHorizontalMap_spec
#print axioms StrictEUnit.v5_descentOfHorizontalMap_unique

#print axioms StrictEUnit.v5_tensorDerivation_assoc
#print axioms StrictEUnit.v5_tensorDerivation_map_right
#print axioms StrictEUnit.v5_mixedChartPullback
#print axioms StrictEUnit.v5_mixedChartPullback_horizontal
#print axioms StrictEUnit.v5_mixedHorizontalMap
#print axioms StrictEUnit.v5_mixedHorizontalMap_spec

#print axioms StrictEUnit.v5_mixedHorizontalMap_square
