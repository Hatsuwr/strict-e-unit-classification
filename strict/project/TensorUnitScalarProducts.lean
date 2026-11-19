import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! Finite independent expansions of actual tensors and the algebraic last step
of the product-unit argument. Scalarity of all coefficient products is an
explicit hypothesis; this file does not establish that geometric input. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace StrictEUnit
variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- An actual tensor has a finite expansion with independent left coefficients. -/
structure FiniteTensorExpansion (x : A ⊗[k] B) where
  size : ℕ
  left : Fin size → A
  right : Fin size → B
  independent : LinearIndependent k left
  reconstruction : ∑ i, left i ⊗ₜ[k] right i = x

/-- This constructs coefficient data, rather than assuming finite independent
representability of a supplied tensor. -/
def finiteTensorExpansion (x : A ⊗[k] B) : FiniteTensorExpansion x := by
  classical
  let e := Basis.ofVectorSpace k A
  let c := TensorProduct.equivFinsuppOfBasisLeft (N := B) e x
  let f := (Fintype.equivFin ↥c.support).symm
  refine ⟨Fintype.card ↥c.support, (fun i => e (f i).val),
    (fun i => c (f i).val), ?_, ?_⟩
  · exact e.linearIndependent.comp (fun i => (f i).val)
      (Subtype.val_injective.comp f.injective)
  · change ∑ i, (fun j : ↥c.support => e j.val ⊗ₜ[k] c j.val) (f i) = x
    apply (f.sum_comp (fun j : ↥c.support => e j.val ⊗ₜ[k] c j.val)).trans
    calc
      ∑ i : ↥c.support, e i.val ⊗ₜ[k] c i.val = c.sum (fun i b => e i ⊗ₜ[k] b) := by
        exact Finset.sum_coe_sort c.support (fun i => e i ⊗ₜ[k] c i)
      _ = x := by
        rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
        exact (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply x

/-- Nonzero finite tensor expansions contain a nonzero right coefficient. -/
theorem FiniteTensorExpansion.exists_right_ne_zero {x : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (hx : x ≠ 0) :
    ∃ i, d.right i ≠ 0 := by
  classical
  by_contra! h
  apply hx
  rw [← d.reconstruction]
  simp only [h, TensorProduct.tmul_zero, Finset.sum_const_zero]

/-- Multiplication of the actual two expansions gives the double coefficient sum. -/
theorem FiniteTensorExpansion.product_reconstruction {x y : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y) :
    ∑ i, ∑ j, (d.left i * e.left j) ⊗ₜ[k] (d.right i * e.right j) = x * y := by
  classical
  calc
    _ = (∑ i, d.left i ⊗ₜ[k] d.right i) *
        (∑ j, e.left j ⊗ₜ[k] e.right j) := by
      simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
      exact Finset.sum_comm
    _ = x * y := congrArg₂ (· * ·) d.reconstruction e.reconstruction

/-- The actual coefficient-product matrix has vanishing two-by-two minors. -/
theorem coefficient_products_minors {I J : Type*} (α : I → B) (β : J → B)
    (i i' : I) (j j' : J) :
    (α i * β j) * (α i' * β j') = (α i * β j') * (α i' * β j) := by
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- Coordinate relations for an actual inverse pair, in any basis of A.
These are precisely the linear relations imposed on the universal coefficient ring. -/
theorem FiniteTensorExpansion.product_coordinate_relation {x y : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y) (hxy : x * y = 1)
    {Γ : Type*} (basis : Basis Γ k A) (γ : Γ) :
    ∑ i, ∑ j, basis.repr (d.left i * e.left j) γ • (d.right i * e.right j) =
      basis.repr (1 : A) γ • (1 : B) := by
  classical
  have h := congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft basis z γ)
    (d.product_reconstruction e)
  simpa only [map_sum, Finsupp.finset_sum_apply,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, hxy,
    Algebra.TensorProduct.one_def] using h

/-- A single nonzero scalar coefficient product forces every left factor of
the products to lie on one k-line. This uses domain cancellation in B. -/
theorem proportional_of_scalar_products [IsDomain B] {I J : Type*}
    (α : I → B) (β : J → B) (i₀ : I) (j₀ : J)
    (hi : α i₀ ≠ 0) (hj : β j₀ ≠ 0)
    (hscalar : ∀ i j, ∃ c : k, algebraMap k B c = α i * β j) :
    ∃ r : I → k, ∀ i, α i = r i • α i₀ := by
  choose c hc using fun i => hscalar i j₀
  have hc0 : c i₀ ≠ 0 := by
    intro h
    have hh := hc i₀
    rw [h, map_zero] at hh
    exact mul_ne_zero hi hj hh.symm
  refine ⟨fun i => c i / c i₀, fun i => ?_⟩
  apply mul_right_cancel₀ hj
  calc
    α i * β j₀ = algebraMap k B (c i) := (hc i).symm
    _ = algebraMap k B (c i / c i₀) * algebraMap k B (c i₀) := by
      rw [← map_mul, div_mul_cancel₀ _ hc0]
    _ = ((c i / c i₀) • α i₀) * β j₀ := by
      rw [Algebra.smul_def, mul_assoc, hc i₀]

/-- Nonzero tensors with scalar pairwise coefficient products are pure.
No tensor-factorization premise is used. Independence is only needed by the
separate geometric argument that is to establish the scalar-product premise. -/
theorem pure_tensor_of_scalar_coefficient_products [IsDomain B]
    {x y : A ⊗[k] B} (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hscalar : ∀ i j, ∃ c : k,
      algebraMap k B c = d.right i * e.right j) :
    ∃ a : A, ∃ b : B, x = a ⊗ₜ[k] b := by
  classical
  obtain ⟨i₀, hi⟩ := d.exists_right_ne_zero hx
  obtain ⟨j₀, hj⟩ := e.exists_right_ne_zero hy
  obtain ⟨r, hr⟩ := proportional_of_scalar_products d.right e.right i₀ j₀ hi hj hscalar
  refine ⟨∑ i, r i • d.left i, d.right i₀, ?_⟩
  apply d.reconstruction.symm.trans
  rw [TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- Over a field, nonzero algebras have a nonzero tensor product. -/
theorem tensor_nontrivial_of_nontrivial [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[k] B) :=
  (Algebra.TensorProduct.includeRight_injective (B := B)
    (RingHom.injective (algebraMap k A))).nontrivial

/-- Apply the algebraic reduction to the actual unit and its actual inverse.
Only coefficient scalarity remains as an explicit mathematical hypothesis. -/
theorem unit_pure_of_scalar_coefficient_products [Nontrivial A] [IsDomain B]
    (u : (A ⊗[k] B)ˣ)
    (hscalar : ∀ i j, ∃ c : k, algebraMap k B c =
      (finiteTensorExpansion (u : A ⊗[k] B)).right i *
      (finiteTensorExpansion (↑u⁻¹ : A ⊗[k] B)).right j) :
    ∃ a : A, ∃ b : B, (u : A ⊗[k] B) = a ⊗ₜ[k] b := by
  letI := tensor_nontrivial_of_nontrivial (k := k) (A := A) (B := B)
  exact pure_tensor_of_scalar_coefficient_products
    (finiteTensorExpansion (u : A ⊗[k] B))
    (finiteTensorExpansion (↑u⁻¹ : A ⊗[k] B)) u.ne_zero u⁻¹.ne_zero hscalar

end StrictEUnit
#print axioms StrictEUnit.FiniteTensorExpansion
#print axioms StrictEUnit.finiteTensorExpansion
#print axioms StrictEUnit.FiniteTensorExpansion.exists_right_ne_zero
#print axioms StrictEUnit.proportional_of_scalar_products
#print axioms StrictEUnit.pure_tensor_of_scalar_coefficient_products
#print axioms StrictEUnit.tensor_nontrivial_of_nontrivial
#print axioms StrictEUnit.unit_pure_of_scalar_coefficient_products
#print axioms StrictEUnit.FiniteTensorExpansion.product_reconstruction
#print axioms StrictEUnit.coefficient_products_minors
#print axioms StrictEUnit.FiniteTensorExpansion.product_coordinate_relation
