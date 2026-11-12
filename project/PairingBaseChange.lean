import InvariantDescent

/-!
# Compatibility of scalar multiplication pairings with base change

The tensor distribution and scalar unitor below are explicit equivalences.
The final implication uses actual extended weight spaces and actual products
in the extended algebra. No bialgebra structure on the scalar extension is
assumed. Injectivity of the new scalar inclusion is derived by flat ascent
in the final specialization. A torsor chart must still supply a surjective
extended pairing with the displayed product compatibility.
-/

open scoped TensorProduct
open TensorProduct

noncomputable section

namespace StrictEUnit

section TensorPairing

variable {B : Type*} [CommRing B]
variable (A : Type*) [CommRing A] [Algebra B A]
variable (M N : Type*) [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N]

/-- Explicit tensor distribution: the two new scalar factors are multiplied,
while the original module factors retain their B-tensor product. -/
def tensorPairingBaseChangeEquiv :
    (A ⊗[B] M) ⊗[A] (A ⊗[B] N) ≃ₗ[A] A ⊗[B] (M ⊗[B] N) :=
  (AlgebraTensorModule.tensorTensorTensorComm B A A M A N).trans
    (AlgebraTensorModule.congr (TensorProduct.lid A A)
      (LinearEquiv.refl B (M ⊗[B] N)))

@[simp] theorem tensorPairingBaseChangeEquiv_tmul
    (a b : A) (m : M) (n : N) :
    tensorPairingBaseChangeEquiv A M N ((a ⊗ₜ[B] m) ⊗ₜ[A] (b ⊗ₜ[B] n)) =
      (a * b) ⊗ₜ[B] (m ⊗ₜ[B] n) := by
  simp only [tensorPairingBaseChangeEquiv, LinearEquiv.trans_apply,
    AlgebraTensorModule.tensorTensorTensorComm_tmul, AlgebraTensorModule.congr_tmul,
    TensorProduct.lid_tmul, LinearEquiv.refl_apply, smul_eq_mul]

/-- The scalar unitor is A-linear; it sends a tensor b to b acting on a. -/
def scalarBaseChangeEquiv : A ⊗[B] B ≃ₗ[A] A :=
  AlgebraTensorModule.rid B A A

@[simp] theorem scalarBaseChangeEquiv_tmul (a : A) (b : B) :
    scalarBaseChangeEquiv (B := B) A (a ⊗ₜ[B] b) = b • a := rfl

variable {M N}

/-- The scalar-valued extension of a pairing, with all tensor reassociation
and the scalar unitor included explicitly. -/
def scalarPairingBaseChange (μ : M ⊗[B] N →ₗ[B] B) :
    (A ⊗[B] M) ⊗[A] (A ⊗[B] N) →ₗ[A] A :=
  (scalarBaseChangeEquiv (B := B) A).toLinearMap.comp
    ((AlgebraTensorModule.lTensor A A μ).comp
      (tensorPairingBaseChangeEquiv A M N).toLinearMap)

@[simp] theorem scalarPairingBaseChange_tmul
    (μ : M ⊗[B] N →ₗ[B] B) (a b : A) (m : M) (n : N) :
    scalarPairingBaseChange A μ ((a ⊗ₜ[B] m) ⊗ₜ[A] (b ⊗ₜ[B] n)) =
      μ (m ⊗ₜ[B] n) • (a * b) := by
  simp only [scalarPairingBaseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorPairingBaseChangeEquiv_tmul, AlgebraTensorModule.lTensor_tmul,
    scalarBaseChangeEquiv_tmul]

/-- Surjectivity of the scalar-valued extension implies surjectivity of the
literal tensor-extended map used in faithful-flat descent. -/
theorem lTensor_surjective_of_scalarPairingBaseChange
    (μ : M ⊗[B] N →ₗ[B] B)
    (hμ : Function.Surjective (scalarPairingBaseChange A μ)) :
    Function.Surjective (μ.lTensor A) := by
  intro z
  obtain ⟨t, ht⟩ := hμ (scalarBaseChangeEquiv (B := B) A z)
  refine ⟨tensorPairingBaseChangeEquiv A M N t, ?_⟩
  apply (scalarBaseChangeEquiv (B := B) A).injective
  exact ht

end TensorPairing

section WeightPairing

variable {B R T : Type*} [CommRing B] [CommRing R] [CommRing T]
  [Algebra B R] [Algebra B T]
variable (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
variable (ρ ι : R →ₐ[B] T) (χ ψ : T)

/-- The two canonical weight-space base-change equivalences induce the
canonical equivalence on their A-tensor product. -/
def weightPairTensorBaseChangeEquiv :
    (A ⊗[B] weightSpace ρ ι χ) ⊗[A] (A ⊗[B] weightSpace ρ ι ψ) ≃ₗ[A]
      (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] χ)) ⊗[A]
      (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] ψ)) :=
  TensorProduct.congr (actualWeightSpaceBaseChangeEquiv A ρ ι χ)
    (actualWeightSpaceBaseChangeEquiv A ρ ι ψ)

/-- Any scalar-valued pairing on the actual extended weight spaces which
agrees with ambient multiplication equals the extended original pairing.
Injectivity of the new scalar inclusion is used only to identify scalars.
No invariant-ring hypothesis for the extended algebra is required. -/
theorem extended_weight_pairing_compatibility
    (hinjA : Function.Injective (algebraMap A (A ⊗[B] R)))
    (μ : weightSpace ρ ι χ ⊗[B] weightSpace ρ ι ψ →ₗ[B] B)
    (hμ : ∀ (m : weightSpace ρ ι χ) (n : weightSpace ρ ι ψ),
      algebraMap B R (μ (m ⊗ₜ[B] n)) = (m : R) * (n : R))
    (ν : (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] χ)) ⊗[A]
      (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] ψ)) →ₗ[A] A)
    (hν : ∀ m n, algebraMap A (A ⊗[B] R) (ν (m ⊗ₜ[A] n)) =
      (m : A ⊗[B] R) * (n : A ⊗[B] R)) :
    ν.comp (weightPairTensorBaseChangeEquiv A ρ ι χ ψ).toLinearMap =
      scalarPairingBaseChange A μ := by
  apply TensorProduct.ext'
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b n =>
          apply hinjA
          change algebraMap A (A ⊗[B] R)
              (ν ((actualWeightSpaceBaseChangeEquiv A ρ ι χ) (a ⊗ₜ[B] m) ⊗ₜ[A]
                (actualWeightSpaceBaseChangeEquiv A ρ ι ψ) (b ⊗ₜ[B] n))) = _
          rw [hν, actualWeightSpaceBaseChangeEquiv_tmul,
            actualWeightSpaceBaseChangeEquiv_tmul, scalarPairingBaseChange_tmul]
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          change (a * b) ⊗ₜ[B] ((m : R) * (n : R)) =
            (μ (m ⊗ₜ[B] n) • (a * b)) ⊗ₜ[B] (1 : R)
          rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hμ]
      | add y z hy hz => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hy hz
  | add x z hx hz => simpa only [add_tmul, map_add] using congrArg₂ (· + ·) hx hz

/-- Actual extended-weight multiplication surjectivity supplies precisely
the local tensor-map surjectivity needed by the regular-unit theorem. -/
theorem lTensor_surjective_of_extended_weight_pairing
    (hinjA : Function.Injective (algebraMap A (A ⊗[B] R)))
    (μ : weightSpace ρ ι χ ⊗[B] weightSpace ρ ι ψ →ₗ[B] B)
    (hμ : ∀ (m : weightSpace ρ ι χ) (n : weightSpace ρ ι ψ),
      algebraMap B R (μ (m ⊗ₜ[B] n)) = (m : R) * (n : R))
    (ν : (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] χ)) ⊗[A]
      (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] ψ)) →ₗ[A] A)
    (hν : ∀ m n, algebraMap A (A ⊗[B] R) (ν (m ⊗ₜ[A] n)) =
      (m : A ⊗[B] R) * (n : A ⊗[B] R))
    (hsurj : Function.Surjective ν) : Function.Surjective (μ.lTensor A) := by
  apply lTensor_surjective_of_scalarPairingBaseChange A μ
  rw [← extended_weight_pairing_compatibility A ρ ι χ ψ hinjA μ hμ ν hν]
  exact hsurj.comp (weightPairTensorBaseChangeEquiv A ρ ι χ ψ).surjective

end WeightPairing

section ScalarWeightPairing

variable {B R T : Type*} [CommRing B] [CommRing R] [CommRing T]
  [Algebra B R] [Algebra B T]

/-- Direct application to the constructed opposite-weight scalar pairing.
The original multiplication compatibility is discharged by its checked
construction, not repeated as an additional premise. The extended pairing
can be supplied by a chart without an extended invariant-ring hypothesis. -/
theorem scalarWeightPairing_lTensor_surjective_of_extended_pairing
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r)
    (ν : (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] (χ : T))) ⊗[A]
      (weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] (↑χ⁻¹ : T))) →ₗ[A] A)
    (hν : ∀ m n, algebraMap A (A ⊗[B] R) (ν (m ⊗ₜ[A] n)) =
      (m : A ⊗[B] R) * (n : A ⊗[B] R))
    (hsurj : Function.Surjective ν) :
    Function.Surjective ((scalarWeightPairing ρ ι χ hinj hfixed).lTensor A) :=
  lTensor_surjective_of_extended_weight_pairing A ρ ι (χ : T) (↑χ⁻¹ : T)
    (scalar_inclusion_injective_ascends A ρ ι hinj)
    (scalarWeightPairing ρ ι χ hinj hfixed)
    (scalarWeightPairing_tmul ρ ι χ hinj hfixed) ν hν hsurj

end ScalarWeightPairing

end StrictEUnit

#print axioms StrictEUnit.tensorPairingBaseChangeEquiv
#print axioms StrictEUnit.tensorPairingBaseChangeEquiv_tmul
#print axioms StrictEUnit.scalarBaseChangeEquiv
#print axioms StrictEUnit.scalarBaseChangeEquiv_tmul
#print axioms StrictEUnit.scalarPairingBaseChange
#print axioms StrictEUnit.scalarPairingBaseChange_tmul
#print axioms StrictEUnit.lTensor_surjective_of_scalarPairingBaseChange
#print axioms StrictEUnit.weightPairTensorBaseChangeEquiv
#print axioms StrictEUnit.extended_weight_pairing_compatibility
#print axioms StrictEUnit.lTensor_surjective_of_extended_weight_pairing
#print axioms StrictEUnit.scalarWeightPairing_lTensor_surjective_of_extended_pairing
