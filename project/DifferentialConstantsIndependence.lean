import BaseFractionConstants
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Linear independence of differential constants survives extension from
the exact constant field. The proof normalizes a finite relation and
inducts on its support; no linear-disjointness hypothesis is assumed. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {k E S ι : Type*} [Field k] [Field E] [CommRing S]
  [Algebra k E] [Algebra E S] [Algebra k S] [IsScalarTower k E S]
  [Algebra ℤ E] [Algebra ℤ S]

/-- Differentiate a linear combination of constant vectors coefficientwise. -/
theorem derivation_constant_sum
    (dE : Derivation ℤ E E) (dS : Derivation ℤ S S)
    (hcomp : ∀ a : E, dS (algebraMap E S a) = algebraMap E S (dE a))
    (v : ι → S) (hv : ∀ i, dS (v i) = 0)
    (s : Finset ι) (f : ι → E) :
    dS (∑ i ∈ s, f i • v i) = ∑ i ∈ s, dE (f i) • v i := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Algebra.smul_def, dS.leibniz, hcomp, hv, smul_eq_mul, mul_zero, zero_add]
  change v i * algebraMap E S (dE (f i)) = algebraMap E S (dE (f i)) * v i
  exact mul_comm _ _

/-- Constants which are k-linearly independent remain E-linearly independent
when E has no constants outside k and the ambient derivation is compatible. -/
theorem differential_constants_linearIndependent
    (dE : Derivation ℤ E E) (dS : Derivation ℤ S S)
    (hcomp : ∀ a : E, dS (algebraMap E S a) = algebraMap E S (dE a))
    (hconstants : ∀ a : E, dE a = 0 → ∃ c : k, algebraMap k E c = a)
    (v : ι → S) (hv : ∀ i, dS (v i) = 0)
    (hli : LinearIndependent k v) : LinearIndependent E v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro f hf
    have hfa : f a = 0 := by
      by_contra hfa
      let g : ι → E := fun i => (f a)⁻¹ * f i
      have hga : g a = 1 := inv_mul_cancel₀ hfa
      have hg : ∑ i ∈ insert a s, g i • v i = 0 := by
        calc
          ∑ i ∈ insert a s, g i • v i = (f a)⁻¹ • (∑ i ∈ insert a s, f i • v i) := by
            simp only [Finset.smul_sum, smul_smul, g]
          _ = 0 := by rw [hf, smul_zero]
      have hDga : dE (g a) = 0 := by rw [hga, dE.map_one_eq_zero]
      have hdrel := congrArg dS hg
      rw [derivation_constant_sum dE dS hcomp v hv, map_zero,
        Finset.sum_insert ha, hDga, zero_smul, zero_add] at hdrel
      have hDg : ∀ i ∈ insert a s, dE (g i) = 0 := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hDga
        · exact ih (fun j => dE (g j)) hdrel i hi
      have hex : ∀ i : ι, ∃ c : k, i ∈ insert a s → algebraMap k E c = g i := by
        intro i
        by_cases hi : i ∈ insert a s
        · obtain ⟨c, hc⟩ := hconstants (g i) (hDg i hi)
          exact ⟨c, fun _ => hc⟩
        · exact ⟨0, fun h => False.elim (hi h)⟩
      choose b hb using hex
      have hkrel : ∑ i ∈ insert a s, b i • v i = 0 := by
        calc
          ∑ i ∈ insert a s, b i • v i = ∑ i ∈ insert a s, g i • v i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hb i hi, IsScalarTower.algebraMap_smul]
          _ = 0 := hg
      have hba : b a = 0 := (linearIndependent_iff'.mp hli) _ b hkrel a (Finset.mem_insert_self _ _)
      have hzero : g a = 0 := by
        rw [← hb a (Finset.mem_insert_self _ _), hba, map_zero]
      exact one_ne_zero (hga.symm.trans hzero)
    rw [Finset.sum_insert ha, hfa, zero_smul, zero_add] at hf
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfa
    · exact ih f hf i hi

/-- Injectivity can be checked on the image of an entire basis. -/
theorem linearMap_injective_of_basis_image
    {F V W J : Type*} [Field F] [AddCommGroup V] [AddCommGroup W]
    [Module F V] [Module F W] (b : Basis J F V) (f : V →ₗ[F] W)
    (h : LinearIndependent F (fun j => f (b j))) : Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hrepr : Finsupp.linearCombination F (fun j => f (b j)) (b.repr x) = f x := by
    calc
      _ = f (Finsupp.linearCombination F b (b.repr x)) := by
        simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
      _ = f x := congrArg f (b.linearCombination_repr x)
  have hz : b.repr x = 0 := (linearIndependent_iff.mp h) _ (hrepr.trans hx)
  exact b.repr.injective (by simpa only [map_zero] using hz)

open scoped TensorProduct

/-- The actual multiplication map from the scalar extension of a subalgebra. -/
def constantsTensorMap (C : Subalgebra k S) : E ⊗[k] C →ₐ[E] S :=
  Algebra.TensorProduct.lift (Algebra.ofId E S) C.val (fun _ _ => Commute.all _ _)

omit [Algebra ℤ E] [Algebra ℤ S] in
@[simp] theorem constantsTensorMap_tmul (C : Subalgebra k S) (a : E) (c : C) :
    constantsTensorMap (E:=E) C (a ⊗ₜ[k] c) = algebraMap E S a * (c:S) := rfl

/-- Multiplication E tensor C → S is injective for every subalgebra C of
actual differential constants. Neither injectivity nor linear disjointness
is assumed. -/
theorem differential_constants_tensor_injective
    (dE : Derivation ℤ E E) (dS : Derivation ℤ S S)
    (hcomp : ∀ a : E, dS (algebraMap E S a) = algebraMap E S (dE a))
    (hconstants : ∀ a : E, dE a = 0 → ∃ c : k, algebraMap k E c = a)
    (C : Subalgebra k S) (hC : ∀ c : C, dS (c:S) = 0) :
    Function.Injective (constantsTensorMap (E:=E) C) := by
  let b := Module.Free.chooseBasis k C
  have hb : LinearIndependent k (fun i => (b i : S)) :=
    b.linearIndependent.map' C.val.toLinearMap
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hE : LinearIndependent E (fun i => (b i : S)) :=
    differential_constants_linearIndependent dE dS hcomp hconstants _ (fun i => hC (b i)) hb
  apply linearMap_injective_of_basis_image (b.baseChange E)
    (constantsTensorMap (E:=E) C).toLinearMap
  convert hE using 1
  funext i
  simp only [Basis.baseChange_apply, AlgHom.toLinearMap_apply,
    constantsTensorMap_tmul, map_one, one_mul]

/-- The actual subalgebra of elements killed by the ambient derivation. -/
def differentialConstantsSubalgebra (dS : Derivation ℤ S S)
    (hscalar : ∀ c : k, dS (algebraMap k S c) = 0) : Subalgebra k S where
  carrier := {x | dS x = 0}
  zero_mem' := map_zero dS
  one_mem' := dS.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change dS (x+y) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    change dS (x*y) = 0
    rw [dS.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  algebraMap_mem' := hscalar

/-- The multiplication map for the full, actual constants subalgebra is injective. -/
theorem actual_constants_tensor_injective
    (dE : Derivation ℤ E E) (dS : Derivation ℤ S S)
    (hcomp : ∀ a : E, dS (algebraMap E S a) = algebraMap E S (dE a))
    (hconstants : ∀ a : E, dE a = 0 → ∃ c : k, algebraMap k E c = a)
    (hscalar : ∀ c : k, dS (algebraMap k S c) = 0) :
    Function.Injective
      (constantsTensorMap (E:=E) (differentialConstantsSubalgebra dS hscalar)) :=
  differential_constants_tensor_injective dE dS hcomp hconstants _ (fun c => c.property)

/-- Exact base constants and compatibility imply that ambient k-scalars
are constants; this is not an additional hypothesis. -/
theorem compatible_scalar_constants
    (dE : Derivation ℤ E E) (dS : Derivation ℤ S S)
    (hcomp : ∀ a : E, dS (algebraMap E S a) = algebraMap E S (dE a))
    (hconstants : ∀ a : E, dE a = 0 ↔ ∃ c : k, algebraMap k E c = a) :
    ∀ c : k, dS (algebraMap k S c) = 0 := by
  intro c
  rw [IsScalarTower.algebraMap_apply k E S, hcomp,
    (hconstants (algebraMap k E c)).mpr ⟨c, rfl⟩, map_zero]

/-- Final injectivity statement for the full constants subalgebra, from
only exact base constants and differential compatibility. -/
theorem full_constants_tensor_injective
    (dE : Derivation ℤ E E) (dS : Derivation ℤ S S)
    (hcomp : ∀ a : E, dS (algebraMap E S a) = algebraMap E S (dE a))
    (hconstants : ∀ a : E, dE a = 0 ↔ ∃ c : k, algebraMap k E c = a) :
    Function.Injective (constantsTensorMap (E:=E)
      (differentialConstantsSubalgebra dS
        (compatible_scalar_constants dE dS hcomp hconstants))) :=
  actual_constants_tensor_injective dE dS hcomp (fun a => (hconstants a).mp)
    (compatible_scalar_constants dE dS hcomp hconstants)

end StrictEUnit

#print axioms StrictEUnit.derivation_constant_sum
#print axioms StrictEUnit.differential_constants_linearIndependent
#print axioms StrictEUnit.linearMap_injective_of_basis_image
#print axioms StrictEUnit.constantsTensorMap
#print axioms StrictEUnit.constantsTensorMap_tmul
#print axioms StrictEUnit.differential_constants_tensor_injective
#print axioms StrictEUnit.differentialConstantsSubalgebra
#print axioms StrictEUnit.actual_constants_tensor_injective

#print axioms StrictEUnit.compatible_scalar_constants
#print axioms StrictEUnit.full_constants_tensor_injective
