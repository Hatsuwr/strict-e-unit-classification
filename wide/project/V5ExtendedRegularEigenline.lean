import V5ComponentRegularInvariants
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k R H : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [CommRing H] [Bialgebra k H]

/-- First-leg counit contraction of an arbitrary prescribed weight. -/
theorem v5ExtendedRegular_contract_weight (χ : H) (x : R ⊗[k] H) :
    ((TensorProduct.lid k H).toLinearMap.comp
      ((Coalgebra.counit (R := k) (A := H)).rTensor H)).lTensor R
      (((TensorProduct.mk k H H).flip χ).lTensor R x) =
    v5ComponentEval x ⊗ₜ[k] χ := by
  induction x using TensorProduct.induction_on with
  | zero => simp [v5ComponentEval]
  | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
  | tmul r h =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply,
      LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, v5ComponentEval_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- Eigenvectors are exactly the counit coefficient times the chosen weight.
This forward assertion does not even need grouplikeness of χ. -/
theorem v5ExtendedRegular_weight_eq_counit (χ : H) (x : R ⊗[k] H)
    (hx : (Coalgebra.comul (R := k) (A := H)).lTensor R x =
      ((TensorProduct.mk k H H).flip χ).lTensor R x) :
    x = v5ComponentEval x ⊗ₜ[k] χ := by
  have he := congrArg
    (((TensorProduct.lid k H).toLinearMap.comp
      ((Coalgebra.counit (R := k) (A := H)).rTensor H)).lTensor R) hx
  simpa only [v5Component_contract_comul, v5ExtendedRegular_contract_weight] using he

theorem v5ExtendedRegular_weight_iff (χ : H)
    (hχ : Coalgebra.comul (R := k) χ = χ ⊗ₜ[k] χ) (x : R ⊗[k] H) :
    (Coalgebra.comul (R := k) (A := H)).lTensor R x =
      ((TensorProduct.mk k H H).flip χ).lTensor R x ↔
    ∃ r : R, x = r ⊗ₜ[k] χ := by
  constructor
  · intro hx
    exact ⟨v5ComponentEval x, v5ExtendedRegular_weight_eq_counit χ x hx⟩
  · rintro ⟨r, rfl⟩
    simp only [LinearMap.lTensor_tmul, LinearMap.flip_apply, TensorProduct.mk_apply, hχ]

/-- The concrete R-linear equalizer for the coefficient-extended coaction. -/
def v5ExtendedRegularEigenline (χ : H) : Submodule R (R ⊗[k] H) :=
  LinearMap.eqLocus
    (AlgebraTensorModule.lTensor R R (Coalgebra.comul (R := k) (A := H)))
    (AlgebraTensorModule.lTensor R R ((TensorProduct.mk k H H).flip χ))

/-- No flatness, domain, reducedness, points, or algebraic closure assumptions:
the extended regular eigenline is the span of the actual element 1⊗χ. -/
theorem v5ExtendedRegularEigenline_eq_span (χ : H)
    (hχ : Coalgebra.comul (R := k) χ = χ ⊗ₜ[k] χ) :
    v5ExtendedRegularEigenline (R := R) χ =
      Submodule.span R {((1 : R) ⊗ₜ[k] χ)} := by
  ext x
  change ((Coalgebra.comul (R := k) (A := H)).lTensor R x =
    ((TensorProduct.mk k H H).flip χ).lTensor R x) ↔ _
  rw [v5ExtendedRegular_weight_iff χ hχ]
  constructor
  · rintro ⟨r, rfl⟩
    have hm := Submodule.smul_mem (Submodule.span R {((1 : R) ⊗ₜ[k] χ)}) r
      (Submodule.subset_span (Set.mem_singleton _))
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hm
  · intro hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨r, ?_⟩
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hr.symm

/-- Normalization of the character makes the coefficient unique. -/
theorem v5ExtendedRegular_weight_unique_coefficient (χ : H)
    (hε : Coalgebra.counit (R := k) χ = 1) (x : R ⊗[k] H)
    (hx : (Coalgebra.comul (R := k) (A := H)).lTensor R x =
      ((TensorProduct.mk k H H).flip χ).lTensor R x) :
    ∃! r : R, x = r ⊗ₜ[k] χ := by
  refine ⟨v5ComponentEval x, v5ExtendedRegular_weight_eq_counit χ x hx, ?_⟩
  intro r hr
  have he := congrArg (v5ComponentEval (k := k) (R := R) (H := H)) hr
  simpa only [v5ComponentEval_tmul, hε, one_smul] using he.symm

end StrictEUnit
#print axioms StrictEUnit.v5ExtendedRegular_contract_weight
#print axioms StrictEUnit.v5ExtendedRegular_weight_eq_counit
#print axioms StrictEUnit.v5ExtendedRegular_weight_iff
#print axioms StrictEUnit.v5ExtendedRegularEigenline_eq_span

#print axioms StrictEUnit.v5ExtendedRegular_weight_unique_coefficient
