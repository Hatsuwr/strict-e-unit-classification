import PVTransitionConstants
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The genuine subalgebra of diagonal differential constants and the
multiplication map into the relative tensor square. No identification with
a prescribed group coordinate algebra is assumed. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
section Constants
variable {k S n : Type*} [CommRing k] [CommRing S] [Algebra k S]

def derivationConstants (δ : Derivation k S S) : Subalgebra k S where
  carrier := {s | δ s = 0}
  zero_mem' := map_zero δ
  one_mem' := δ.map_one_eq_zero
  add_mem' hx hy := by
    change δ (_ + _) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' hx hy := by
    change δ (_ * _) = 0
    rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  algebraMap_mem' b := δ.map_algebraMap b

@[simp] theorem mem_derivationConstants (δ : Derivation k S S) (s : S) :
    s ∈ derivationConstants δ ↔ δ s = 0 := Iff.rfl

variable [Fintype n] [DecidableEq n]

def constantMatrix (δ : Derivation k S S) (M : Matrix n n S)
    (hM : matrixDerivative δ M = 0) : Matrix n n (derivationConstants δ) :=
  fun i j => ⟨M i j, congrArg (fun N : Matrix n n S => N i j) hM⟩

theorem determinant_mem_constants (δ : Derivation k S S) (M : Matrix n n S)
    (hM : matrixDerivative δ M = 0) :
    M.det ∈ derivationConstants δ := by
  have he := (derivationConstants δ).val.map_det (constantMatrix δ M hM)
  exact he ▸ (constantMatrix δ M hM).det.property

theorem inverse_matrix_constant (δ : Derivation k S S) (M : (Matrix n n S)ˣ)
    (hM : matrixDerivative δ (M : Matrix n n S) = 0) :
    matrixDerivative δ (↑M⁻¹ : Matrix n n S) = 0 := by
  have h := fundamental_matrix_transition_constant δ (0 : Matrix n n S) M
    (1 : Matrix n n S) (by simpa using hM) (by simp)
  simpa using h

theorem inverse_determinant_mem_constants (δ : Derivation k S S)
    (M : (Matrix n n S)ˣ) (hM : matrixDerivative δ (M : Matrix n n S) = 0) :
    Matrix.det (↑M⁻¹ : Matrix n n S) ∈ derivationConstants δ :=
  determinant_mem_constants δ _ (inverse_matrix_constant δ M hM)
end Constants

section Relative
variable {k B R n : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- All actual constants in the relative differential tensor product. -/
def pvConstantAlgebra (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) :
    Subalgebra k (R ⊗[B] R) :=
  derivationConstants (relativeTensorDerivation δB δ hδ)

/-- The natural multiplication map r tensor c ↦ (r tensor 1)c. -/
def pvConstantMultiplication (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) :
    R ⊗[k] pvConstantAlgebra δB δ hδ →ₐ[R] R ⊗[B] R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (R ⊗[B] R))
    (pvConstantAlgebra δB δ hδ).val (fun _ _ => Commute.all _ _)

@[simp] theorem pvConstantMultiplication_tmul
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (r : R) (c : pvConstantAlgebra δB δ hδ) :
    pvConstantMultiplication δB δ hδ (r ⊗ₜ[k] c) =
      (r ⊗ₜ[B] (1 : R)) * (c : R ⊗[B] R) := rfl

variable [Fintype n] [DecidableEq n]

def pvTransitionUnit (Y : (Matrix n n R)ˣ) : (Matrix n n (R ⊗[B] R))ˣ :=
  (leftFundamentalMatrix (B := B) Y)⁻¹ * rightFundamentalMatrix (B := B) Y

theorem pvTransition_entries_mem_constants
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R)) (i j : n) :
    (pvTransitionUnit (B := B) Y : Matrix n n (R ⊗[B] R)) i j ∈
      pvConstantAlgebra δB δ hδ :=
  congrArg (fun M : Matrix n n (R ⊗[B] R) => M i j)
    (pv_transition_matrix_constant δB δ hδ A Y hY)

theorem pvTransition_inverse_entries_mem_constants
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R)) (i j : n) :
    (↑(pvTransitionUnit (B := B) Y)⁻¹ : Matrix n n (R ⊗[B] R)) i j ∈
      pvConstantAlgebra δB δ hδ :=
  congrArg (fun M : Matrix n n (R ⊗[B] R) => M i j)
    (inverse_matrix_constant (relativeTensorDerivation δB δ hδ)
      (pvTransitionUnit Y) (pv_transition_matrix_constant δB δ hδ A Y hY))
end Relative
end StrictEUnit

#print axioms StrictEUnit.derivationConstants
#print axioms StrictEUnit.mem_derivationConstants
#print axioms StrictEUnit.constantMatrix
#print axioms StrictEUnit.determinant_mem_constants
#print axioms StrictEUnit.inverse_matrix_constant
#print axioms StrictEUnit.inverse_determinant_mem_constants
#print axioms StrictEUnit.pvConstantAlgebra
#print axioms StrictEUnit.pvConstantMultiplication
#print axioms StrictEUnit.pvConstantMultiplication_tmul
#print axioms StrictEUnit.pvTransitionUnit
#print axioms StrictEUnit.pvTransition_entries_mem_constants
#print axioms StrictEUnit.pvTransition_inverse_entries_mem_constants
