import WeightSpaces
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# The character calculation on a trivial torsor

This is the coordinate-ring version of f(gh)=f(g)χ(h) ⇒ f(g)=f(1)χ(g).
It uses the actual counit law of a mathlib bialgebra. Consequently it is
an identity of algebraic functions, not a check only at closed points.

Transporting a particular torsor's coaction and multiplication through a
trivializing cover is still a separate obligation.
-/

open TensorProduct
open scoped TensorProduct

noncomputable section

namespace StrictEUnit

variable {B H : Type*} [CommRing B] [CommRing H] [Bialgebra B H]

/-- The counit axiom directly extracts the scalar from a regular-representation
weight vector. No density of points or reducedness assumption is used. -/
theorem regular_weight_eq_counit_smul (χ f : H)
    (hf : Coalgebra.comul (R := B) f = f ⊗ₜ[B] χ) :
    f = Coalgebra.counit (R := B) f • χ := by
  have h := congrArg (TensorProduct.lid B H)
    (congrArg ((Coalgebra.counit (R := B)).rTensor H) hf)
  simpa only [Coalgebra.rTensor_counit_comul, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, one_smul] using h

/-- A grouplike element gives all regular weight vectors by scalar multiples. -/
theorem regular_weight_iff_scalar_multiple (χ f : H)
    (hχ : Coalgebra.comul (R := B) χ = χ ⊗ₜ[B] χ) :
    Coalgebra.comul (R := B) f = f ⊗ₜ[B] χ ↔ ∃ b : B, f = b • χ := by
  constructor
  · intro hf
    exact ⟨Coalgebra.counit (R := B) f, regular_weight_eq_counit_smul χ f hf⟩
  · rintro ⟨b, rfl⟩
    rw [map_smul, hχ, smul_tmul']

/-- The trivial-torsor weight module is the concrete weight equalizer used
elsewhere in this project. -/
def regularWeightSpace (χ : H) : Submodule B H :=
  weightSpace (Bialgebra.comulAlgHom B H)
    (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H)
    (1 ⊗ₜ[B] χ)

@[simp] theorem mem_regularWeightSpace (χ f : H) :
    f ∈ regularWeightSpace (B := B) χ ↔
      Coalgebra.comul (R := B) f = f ⊗ₜ[B] χ := by
  simp only [regularWeightSpace, mem_weightSpace, Bialgebra.comulAlgHom_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- Actual grouplike weight elements generate the entire equalizer. -/
theorem regularWeightSpace_cyclic (χ : H)
    (hχ : Coalgebra.comul (R := B) χ = χ ⊗ₜ[B] χ) :
    ∀ f : regularWeightSpace (B := B) χ,
      ∃ b : B, f = b • (⟨χ, (mem_regularWeightSpace χ χ).mpr hχ⟩ :
        regularWeightSpace (B := B) χ) := by
  intro f
  refine ⟨Coalgebra.counit (R := B) (f : H), ?_⟩
  apply Subtype.ext
  exact regular_weight_eq_counit_smul χ f ((mem_regularWeightSpace χ f).mp f.property)

/-- The counit of a grouplike UNIT is one, so the scalar generator has no
annihilator. This is derived, not added to the character hypotheses. -/
theorem counit_grouplike_unit_eq_one (χ : Hˣ)
    (hχ : Coalgebra.comul (R := B) (χ : H) = (χ : H) ⊗ₜ[B] (χ : H)) :
    Coalgebra.counit (R := B) (χ : H) = 1 := by
  have h : algebraMap B H (Coalgebra.counit (R := B) (χ : H)) = 1 := by
    apply (Units.mul_left_inj χ).mp
    simpa only [Algebra.smul_def, one_mul] using
      (regular_weight_eq_counit_smul (χ : H) (χ : H) hχ).symm
  have hc := congrArg (Coalgebra.counit (R := B)) h
  simpa only [Bialgebra.counit_algebraMap, Bialgebra.counit_one] using hc

/-- The regular-representation character weight module is genuinely free
of rank one, with forward map b ↦ bχ and inverse the counit. -/
def regularWeightEquiv (χ : Hˣ)
    (hχ : Coalgebra.comul (R := B) (χ : H) = (χ : H) ⊗ₜ[B] (χ : H)) :
    B ≃ₗ[B] regularWeightSpace (B := B) (χ : H) where
  toFun b := ⟨b • (χ : H), (mem_regularWeightSpace _ _).mpr
    ((regular_weight_iff_scalar_multiple (χ : H) _ hχ).mpr ⟨b, rfl⟩)⟩
  invFun f := Coalgebra.counit (R := B) (f : H)
  left_inv b := by
    simp only [map_smul, counit_grouplike_unit_eq_one χ hχ, smul_eq_mul, mul_one]
  right_inv f := by
    apply Subtype.ext
    exact (regular_weight_eq_counit_smul (χ : H) f
      ((mem_regularWeightSpace _ _).mp f.property)).symm
  map_add' b c := by ext; exact add_smul b c (χ : H)
  map_smul' b c := by ext; exact mul_smul b c (χ : H)

@[simp] theorem regularWeightEquiv_coe (χ : Hˣ)
    (hχ : Coalgebra.comul (R := B) (χ : H) = (χ : H) ⊗ₜ[B] (χ : H)) (b : B) :
    (regularWeightEquiv χ hχ b : H) = b • (χ : H) := rfl

/-- Inverting a grouplike unit gives a grouplike unit. The proof uses actual
multiplicativity of the coaction and unit cancellation. -/
theorem inverse_grouplike_unit (χ : Hˣ)
    (hχ : Coalgebra.comul (R := B) (χ : H) = (χ : H) ⊗ₜ[B] (χ : H)) :
    Coalgebra.comul (R := B) (↑χ⁻¹ : H) = (↑χ⁻¹ : H) ⊗ₜ[B] (↑χ⁻¹ : H) := by
  let ψ : (H ⊗[B] H)ˣ := Units.map
    (Algebra.TensorProduct.includeRight : H →ₐ[B] H ⊗[B] H).toMonoidHom χ
  have hm : (χ : H) ∈ weightSpace (Bialgebra.comulAlgHom B H)
      (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) (ψ : H ⊗[B] H) := by
    change Coalgebra.comul (R := B) (χ : H) =
      ((χ : H) ⊗ₜ[B] (1 : H)) * ((1 : H) ⊗ₜ[B] (χ : H))
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hχ
  have hi := inverse_unit_opposite_weight (Bialgebra.comulAlgHom B H)
    (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) ψ χ hm
  change Coalgebra.comul (R := B) (↑χ⁻¹ : H) =
    ((↑χ⁻¹ : H) ⊗ₜ[B] (1 : H)) * ((1 : H) ⊗ₜ[B] (↑χ⁻¹ : H)) at hi
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hi

/-- The bialgebra's base inclusion is injective because the counit is a
left inverse. -/
theorem bialgebra_base_injective : Function.Injective (algebraMap B H) := by
  intro x y h
  have hh := congrArg (Coalgebra.counit (R := B)) h
  simpa only [Bialgebra.counit_algebraMap] using hh

/-- The invariant functions on the regular representation are exactly
base scalars, proved using the counit rather than postulated. -/
theorem regular_invariants_are_scalars (f : H)
    (hf : Coalgebra.comul (R := B) f = f ⊗ₜ[B] (1 : H)) :
    algebraMap B H (Coalgebra.counit (R := B) f) = f := by
  simpa only [Algebra.smul_def, mul_one] using
    (regular_weight_eq_counit_smul (1 : H) f hf).symm

/-- The scalar-valued multiplication pairing on the regular representation,
defined by multiplying in H and applying its counit. -/
def regularWeightPairing (χ : Hˣ) :
    regularWeightSpace (B := B) (χ : H) ⊗[B]
      regularWeightSpace (B := B) (↑χ⁻¹ : H) →ₗ[B] B :=
  TensorProduct.lift
    (((LinearMap.mul B H).compl₁₂ (regularWeightSpace (B := B) (χ : H)).subtype
      (regularWeightSpace (B := B) (↑χ⁻¹ : H)).subtype).compr₂
        (Coalgebra.counit (R := B)))

@[simp] theorem regularWeightPairing_tmul (χ : Hˣ)
    (x : regularWeightSpace (B := B) (χ : H))
    (y : regularWeightSpace (B := B) (↑χ⁻¹ : H)) :
    regularWeightPairing χ (x ⊗ₜ[B] y) =
      Coalgebra.counit (R := B) ((x : H) * (y : H)) := rfl

/-- This counit-valued pairing really is multiplication into the scalar
subring. It is not an arbitrary bilinear form on isomorphic modules. -/
theorem regularWeightPairing_product (χ : Hˣ)
    (x : regularWeightSpace (B := B) (χ : H))
    (y : regularWeightSpace (B := B) (↑χ⁻¹ : H)) :
    algebraMap B H (regularWeightPairing χ (x ⊗ₜ[B] y)) = (x : H) * (y : H) := by
  have hx := regular_weight_eq_counit_smul (χ : H) (x : H)
    ((mem_regularWeightSpace _ _).mp x.property)
  have hy := regular_weight_eq_counit_smul (↑χ⁻¹ : H) (y : H)
    ((mem_regularWeightSpace _ _).mp y.property)
  rw [Algebra.smul_def] at hx hy
  rw [regularWeightPairing_tmul, Bialgebra.counit_mul, map_mul]
  calc
    algebraMap B H (Coalgebra.counit (R := B) (x : H)) *
        algebraMap B H (Coalgebra.counit (R := B) (y : H)) =
      (algebraMap B H (Coalgebra.counit (R := B) (x : H)) * (χ : H)) *
        (algebraMap B H (Coalgebra.counit (R := B) (y : H)) * (↑χ⁻¹ : H)) := by
          rw [mul_mul_mul_comm, Units.mul_inv, mul_one]
    _ = (x : H) * (y : H) := by rw [← hx, ← hy]

/-- On the trivial torsor, opposite-character multiplication is surjective:
the pure tensor χ ⊗ χ⁻¹ maps to one. This is exactly the local surjectivity
needed by the faithful-flat regular-unit construction. -/
theorem regularWeightPairing_surjective (χ : Hˣ)
    (hχ : Coalgebra.comul (R := B) (χ : H) = (χ : H) ⊗ₜ[B] (χ : H)) :
    Function.Surjective (regularWeightPairing (B := B) χ) := by
  let x : regularWeightSpace (B := B) (χ : H) :=
    ⟨χ, (mem_regularWeightSpace _ _).mpr hχ⟩
  let y : regularWeightSpace (B := B) (↑χ⁻¹ : H) :=
    ⟨↑χ⁻¹, (mem_regularWeightSpace _ _).mpr (inverse_grouplike_unit χ hχ)⟩
  have hxy : regularWeightPairing χ (x ⊗ₜ[B] y) = 1 := by
    simp only [regularWeightPairing_tmul, x, y, Units.mul_inv, Bialgebra.counit_one]
  intro b
  refine ⟨b • (x ⊗ₜ[B] y), ?_⟩
  rw [map_smul, hxy, smul_eq_mul, mul_one]

end StrictEUnit

#print axioms StrictEUnit.regular_weight_eq_counit_smul
#print axioms StrictEUnit.regular_weight_iff_scalar_multiple
#print axioms StrictEUnit.mem_regularWeightSpace
#print axioms StrictEUnit.regularWeightSpace_cyclic
#print axioms StrictEUnit.counit_grouplike_unit_eq_one
#print axioms StrictEUnit.regularWeightEquiv
#print axioms StrictEUnit.regularWeightEquiv_coe
#print axioms StrictEUnit.inverse_grouplike_unit
#print axioms StrictEUnit.bialgebra_base_injective
#print axioms StrictEUnit.regular_invariants_are_scalars
#print axioms StrictEUnit.regularWeightPairing_tmul
#print axioms StrictEUnit.regularWeightPairing_product
#print axioms StrictEUnit.regularWeightPairing_surjective
