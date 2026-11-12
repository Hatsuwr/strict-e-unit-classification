import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual restriction and quotient of a connection, with proved Leibniz laws.
No projectivity, flatness or existence of a connection is inferred from finiteness. -/
noncomputable section
namespace StrictEUnit
variable {k B M : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]

/-- Restrict an actual connection to a stable B-submodule. -/
def restrictConnection (P : Submodule B M) (nabla : M →ₗ[k] M)
    (hP : ∀ m ∈ P, nabla m ∈ P) : P →ₗ[k] P where
  toFun m := ⟨nabla m, hP m m.property⟩
  map_add' x y := Subtype.ext (nabla.map_add x y)
  map_smul' c x := Subtype.ext (nabla.map_smul c x)

@[simp] theorem restrictConnection_coe (P : Submodule B M) (nabla : M →ₗ[k] M)
    (hP : ∀ m ∈ P, nabla m ∈ P) (m : P) :
    (restrictConnection P nabla hP m : M) = nabla m := rfl

theorem restrictConnection_leibniz (δ : Derivation k B B)
    (P : Submodule B M) (nabla : M →ₗ[k] M)
    (hP : ∀ m ∈ P, nabla m ∈ P)
    (hL : ∀ (b : B) (m : M), nabla (b • m) = δ b • m + b • nabla m)
    (b : B) (m : P) :
    restrictConnection P nabla hP (b • m) =
      δ b • m + b • restrictConnection P nabla hP m :=
  Subtype.ext (hL b m)

/-- Descend the actual k-linear connection through the actual stable quotient.
Restriction-of-scalars equivalences preserve the intended B-module quotient. -/
def quotientConnection (P : Submodule B M) (nabla : M →ₗ[k] M)
    (hP : ∀ m ∈ P, nabla m ∈ P) : (M ⧸ P) →ₗ[k] (M ⧸ P) :=
  let e := Submodule.Quotient.restrictScalarsEquiv k P
  e.toLinearMap.comp (((P.restrictScalars k).mapQ (P.restrictScalars k)
    nabla hP).comp e.symm.toLinearMap)

@[simp] theorem quotientConnection_mk (P : Submodule B M) (nabla : M →ₗ[k] M)
    (hP : ∀ m ∈ P, nabla m ∈ P) (m : M) :
    quotientConnection P nabla hP (P.mkQ m) = P.mkQ (nabla m) := by
  simp only [quotientConnection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply,
    Submodule.Quotient.restrictScalarsEquiv_mk, Submodule.mkQ_apply]

theorem quotientConnection_leibniz (δ : Derivation k B B)
    (P : Submodule B M) (nabla : M →ₗ[k] M)
    (hP : ∀ m ∈ P, nabla m ∈ P)
    (hL : ∀ (b : B) (m : M), nabla (b • m) = δ b • m + b • nabla m)
    (b : B) (q : M ⧸ P) :
    quotientConnection P nabla hP (b • q) =
      δ b • q + b • quotientConnection P nabla hP q := by
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    change quotientConnection P nabla hP (b • P.mkQ m) =
      δ b • P.mkQ m + b • quotientConnection P nabla hP (P.mkQ m)
    rw [← map_smul, quotientConnection_mk, hL, map_add, map_smul,
      map_smul, quotientConnection_mk]
end StrictEUnit
#print axioms StrictEUnit.restrictConnection
#print axioms StrictEUnit.restrictConnection_coe
#print axioms StrictEUnit.restrictConnection_leibniz
#print axioms StrictEUnit.quotientConnection
#print axioms StrictEUnit.quotientConnection_mk
#print axioms StrictEUnit.quotientConnection_leibniz
