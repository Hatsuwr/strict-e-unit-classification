import TensorDerivation

/-! The balanced diagonal derivation over a differential base. The base B
need not consist of constants: its derivative terms match in the balancing
identity. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

def diagonalTensorBilinear (δ : Derivation k R R) : R →+ R →+ R ⊗[B] R where
  toFun r :=
    { toFun := fun s => δ r ⊗ₜ[B] s + r ⊗ₜ[B] δ s
      map_zero' := by simp
      map_add' := by intro s t; simp only [tmul_add, map_add]; abel }
  map_zero' := by ext s; simp
  map_add' r s := by
    ext t
    change δ (r+s) ⊗ₜ[B] t + (r+s) ⊗ₜ[B] δ t =
      (δ r ⊗ₜ[B] t + r ⊗ₜ[B] δ t) + (δ s ⊗ₜ[B] t + s ⊗ₜ[B] δ t)
    simp only [map_add, add_tmul]
    abel

omit [IsScalarTower k B R] in
theorem differential_algebra_smul (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) (b : B) (r : R) :
    δ (b • r) = δB b • r + b • δ r := by
  rw [Algebra.smul_def, Derivation.leibniz, hδ]
  simp only [Algebra.smul_def, smul_eq_mul]
  change algebraMap B R b * δ r + r * algebraMap B R (δB b) =
    algebraMap B R (δB b) * r + algebraMap B R b * δ r
  ring

theorem diagonalTensorBilinear_balanced
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (b : B) (r s : R) :
    diagonalTensorBilinear (B := B) δ (b • r) s =
      diagonalTensorBilinear (B := B) δ r (b • s) := by
  change δ (b • r) ⊗ₜ[B] s + (b • r) ⊗ₜ[B] δ s =
    δ r ⊗ₜ[B] (b • s) + r ⊗ₜ[B] δ (b • s)
  rw [differential_algebra_smul δB δ hδ, differential_algebra_smul δB δ hδ]
  simp only [add_tmul, tmul_add, smul_tmul]
  abel

/-- Additive descent uses balancing, not incorrect B-linearity. -/
def relativeTensorDerivativeAdd (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) :
    R ⊗[B] R →+ R ⊗[B] R :=
  TensorProduct.liftAddHom (diagonalTensorBilinear δ)
    (diagonalTensorBilinear_balanced δB δ hδ)

@[simp] theorem relativeTensorDerivativeAdd_tmul
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) (r s : R) :
    relativeTensorDerivativeAdd δB δ hδ (r ⊗ₜ[B] s) =
      δ r ⊗ₜ[B] s + r ⊗ₜ[B] δ s := rfl

def relativeTensorDerivativeLinear (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) :
    R ⊗[B] R →ₗ[k] R ⊗[B] R :=
  { relativeTensorDerivativeAdd δB δ hδ with
    map_smul' := by
      intro a x
      change relativeTensorDerivativeAdd δB δ hδ (a • x) =
        a • relativeTensorDerivativeAdd δB δ hδ x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r s =>
        simp only [smul_tmul', relativeTensorDerivativeAdd_tmul,
          Derivation.map_smul, smul_add]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

@[simp] theorem relativeTensorDerivativeLinear_tmul
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) (r s : R) :
    relativeTensorDerivativeLinear δB δ hδ (r ⊗ₜ[B] s) =
      δ r ⊗ₜ[B] s + r ⊗ₜ[B] δ s := rfl

theorem relativeTensorDerivativeLinear_mul
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (x y : R ⊗[B] R) :
    relativeTensorDerivativeLinear δB δ hδ (x*y) =
      x * relativeTensorDerivativeLinear δB δ hδ y +
        y * relativeTensorDerivativeLinear δB δ hδ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t u =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, relativeTensorDerivativeLinear_tmul,
        Derivation.leibniz, smul_eq_mul, add_tmul, tmul_add, mul_add,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp only [mul_comm]
      abel
    | add y z hy hz => simp only [mul_add, map_add, add_mul, hy, hz]; abel
  | add x z hx hz => simp only [add_mul, map_add, mul_add, hx, hz]; abel

def relativeTensorDerivation (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) :
    Derivation k (R ⊗[B] R) (R ⊗[B] R) :=
  Derivation.mk' (relativeTensorDerivativeLinear δB δ hδ)
    (relativeTensorDerivativeLinear_mul δB δ hδ)

@[simp] theorem relativeTensorDerivation_tmul
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) (r s : R) :
    relativeTensorDerivation δB δ hδ (r ⊗ₜ[B] s) =
      δ r ⊗ₜ[B] s + r ⊗ₜ[B] δ s := rfl
end StrictEUnit

#print axioms StrictEUnit.diagonalTensorBilinear
#print axioms StrictEUnit.differential_algebra_smul
#print axioms StrictEUnit.diagonalTensorBilinear_balanced
#print axioms StrictEUnit.relativeTensorDerivativeAdd
#print axioms StrictEUnit.relativeTensorDerivativeAdd_tmul
#print axioms StrictEUnit.relativeTensorDerivativeLinear
#print axioms StrictEUnit.relativeTensorDerivativeLinear_tmul
#print axioms StrictEUnit.relativeTensorDerivativeLinear_mul
#print axioms StrictEUnit.relativeTensorDerivation
#print axioms StrictEUnit.relativeTensorDerivation_tmul
