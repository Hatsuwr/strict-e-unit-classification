import RelativeTensorDerivation
import FundamentalMatrixConstants

/-! The two actual copies of a fundamental matrix in the relative tensor
product have a constant transition matrix. This does not assert that these
constants generate a Hopf algebra or that the canonical torsor map is an
isomorphism. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
section Map
variable {k R T n : Type*} [CommRing k] [CommRing R] [CommRing T]
  [Algebra k R] [Algebra k T] [Fintype n] [DecidableEq n]

theorem matrixDerivative_map
    (δ : Derivation k R R) (d : Derivation k T T) (φ : R →+* T)
    (hφ : ∀ r, d (φ r) = φ (δ r)) (M : Matrix n n R) :
    matrixDerivative d (φ.mapMatrix M) = φ.mapMatrix (matrixDerivative δ M) := by
  ext i j
  exact hφ (M i j)

end Map
section Relative
variable {k B R n : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Fintype n] [DecidableEq n]

def leftFundamentalMatrix (Y : (Matrix n n R)ˣ) : (Matrix n n (R ⊗[B] R))ˣ :=
  Units.map ((Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R).toRingHom.mapMatrix).toMonoidHom Y

def rightFundamentalMatrix (Y : (Matrix n n R)ˣ) : (Matrix n n (R ⊗[B] R))ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R).toRingHom.mapMatrix).toMonoidHom Y

/-- Both tensor copies solve the same base-coefficient equation. -/
theorem tensor_fundamental_equations
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R)) :
    matrixDerivative (relativeTensorDerivation δB δ hδ)
        (leftFundamentalMatrix (B := B) Y : Matrix n n (R ⊗[B] R)) =
      (algebraMap B (R ⊗[B] R)).mapMatrix A *
        (leftFundamentalMatrix (B := B) Y : Matrix n n (R ⊗[B] R)) ∧
    matrixDerivative (relativeTensorDerivation δB δ hδ)
        (rightFundamentalMatrix (B := B) Y : Matrix n n (R ⊗[B] R)) =
      (algebraMap B (R ⊗[B] R)).mapMatrix A *
        (rightFundamentalMatrix (B := B) Y : Matrix n n (R ⊗[B] R)) := by
  have hleft : ∀ r, relativeTensorDerivation δB δ hδ
      ((Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R) r) =
      (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R) (δ r) := by
    intro r
    simp only [Algebra.TensorProduct.includeLeft_apply, relativeTensorDerivation_tmul,
      Derivation.map_one_eq_zero, tmul_zero, add_zero]
  have hright : ∀ r, relativeTensorDerivation δB δ hδ
      ((Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R) r) =
      (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R) (δ r) := by
    intro r
    simp only [Algebra.TensorProduct.includeRight_apply, relativeTensorDerivation_tmul,
      Derivation.map_one_eq_zero, zero_tmul, zero_add]
  have hbase (φ : R →ₐ[B] R ⊗[B] R) :
      φ.toRingHom.mapMatrix ((algebraMap B R).mapMatrix A) =
      (algebraMap B (R ⊗[B] R)).mapMatrix A := by
    ext i j
    exact φ.commutes (A i j)
  constructor
  · change matrixDerivative _ ((Algebra.TensorProduct.includeLeft :
      R →ₐ[B] R ⊗[B] R).toRingHom.mapMatrix (Y : Matrix n n R)) = _
    rw [matrixDerivative_map δ _ _ hleft, hY, map_mul, hbase]
    rfl
  · change matrixDerivative _ ((Algebra.TensorProduct.includeRight :
      R →ₐ[B] R ⊗[B] R).toRingHom.mapMatrix (Y : Matrix n n R)) = _
    rw [matrixDerivative_map δ _ _ hright, hY, map_mul, hbase]
    rfl

/-- The actual PV transition matrix has zero diagonal derivative. -/
theorem pv_transition_matrix_constant
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R)) :
    matrixDerivative (relativeTensorDerivation δB δ hδ)
      ((↑(leftFundamentalMatrix (B := B) Y)⁻¹ : Matrix n n (R ⊗[B] R)) *
        (rightFundamentalMatrix (B := B) Y : Matrix n n (R ⊗[B] R))) = 0 := by
  obtain ⟨hleft, hright⟩ := tensor_fundamental_equations δB δ hδ A Y hY
  exact fundamental_matrix_transition_constant _ _ _ _ hleft hright
end Relative
end StrictEUnit

#print axioms StrictEUnit.matrixDerivative_map
#print axioms StrictEUnit.leftFundamentalMatrix
#print axioms StrictEUnit.rightFundamentalMatrix
#print axioms StrictEUnit.tensor_fundamental_equations
#print axioms StrictEUnit.pv_transition_matrix_constant
