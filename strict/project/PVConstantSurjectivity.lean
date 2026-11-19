import PVConstantAlgebra

/-! Surjectivity of the multiplication map under explicit matrix-generation.
Injectivity and a Hopf structure on the constant algebra are not asserted. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
section Determinant
variable {k S n : Type*} [CommRing k] [CommRing S] [Algebra k S]
  [Fintype n] [DecidableEq n]

theorem matrix_det_mem_subalgebra (K : Subalgebra k S) (M : Matrix n n S)
    (hM : ∀ i j, M i j ∈ K) : M.det ∈ K := by
  let M' : Matrix n n K := fun i j => ⟨M i j, hM i j⟩
  have he := K.val.map_det M'
  exact he ▸ M'.det.property
end Determinant

section Relative
variable {k B R n : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Fintype n] [DecidableEq n]

theorem pvConstantMultiplication_left_mem_range
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b)) (r : R) :
    (r ⊗ₜ[B] (1 : R)) ∈ (pvConstantMultiplication δB δ hδ).range :=
  ⟨r ⊗ₜ[k] (1 : pvConstantAlgebra δB δ hδ), by simp⟩

theorem pvConstantMultiplication_constant_mem_range
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (c : R ⊗[B] R) (hc : c ∈ pvConstantAlgebra δB δ hδ) :
    c ∈ (pvConstantMultiplication δB δ hδ).range :=
  ⟨(1 : R) ⊗ₜ[k] (⟨c, hc⟩ : pvConstantAlgebra δB δ hδ), by
    change ((1 : R) ⊗ₜ[B] (1 : R)) * c = c
    rw [← Algebra.TensorProduct.one_def, one_mul]⟩

theorem pvConstantMultiplication_right_matrix_mem_range
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R)) :
    (∀ i j, ((rightFundamentalMatrix (B := B) Y : Matrix n n (R ⊗[B] R)) i j)
      ∈ (pvConstantMultiplication δB δ hδ).range) ∧
    (∀ i j, ((↑(rightFundamentalMatrix (B := B) Y)⁻¹ : Matrix n n (R ⊗[B] R)) i j)
      ∈ (pvConstantMultiplication δB δ hδ).range) := by
  let K := (pvConstantMultiplication δB δ hδ).range
  let L := leftFundamentalMatrix (B := B) Y
  let V := rightFundamentalMatrix (B := B) Y
  let C := pvTransitionUnit (B := B) Y
  have hv : (V : Matrix n n (R ⊗[B] R)) = (L : Matrix n n (R ⊗[B] R)) * C := by
    change _ = (L : Matrix n n (R ⊗[B] R)) * ((↑L⁻¹ : Matrix n n (R ⊗[B] R)) * V)
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hvi : (↑V⁻¹ : Matrix n n (R ⊗[B] R)) =
      (↑C⁻¹ : Matrix n n (R ⊗[B] R)) * (↑L⁻¹ : Matrix n n (R ⊗[B] R)) := by
    change _ = (↑(L⁻¹ * V)⁻¹ : Matrix n n (R ⊗[B] R)) * _
    simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
  constructor
  · intro i j
    change (V : Matrix n n (R ⊗[B] R)) i j ∈ K
    rw [hv, Matrix.mul_apply]
    apply K.sum_mem
    intro a ha
    apply K.mul_mem
    · exact pvConstantMultiplication_left_mem_range δB δ hδ ((Y : Matrix n n R) i a)
    · exact pvConstantMultiplication_constant_mem_range δB δ hδ _
        (pvTransition_entries_mem_constants δB δ hδ A Y hY a j)
  · intro i j
    change (↑V⁻¹ : Matrix n n (R ⊗[B] R)) i j ∈ K
    rw [hvi, Matrix.mul_apply]
    apply K.sum_mem
    intro a ha
    apply K.mul_mem
    · exact pvConstantMultiplication_constant_mem_range δB δ hδ _
        (pvTransition_inverse_entries_mem_constants δB δ hδ A Y hY i a)
    · exact pvConstantMultiplication_left_mem_range δB δ hδ
        ((↑Y⁻¹ : Matrix n n R) a j)

/-- Matrix entries and the inverse determinant suffice for surjectivity.
This proves only surjectivity, not the PV torsor isomorphism. -/
theorem pvConstantMultiplication_surjective
    (δB : Derivation k B B) (δ : Derivation k R R)
    (hδ : ∀ b, δ (algebraMap B R b) = algebraMap B R (δB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R))
    (hgen : Algebra.adjoin B
      (insert (Matrix.det (↑Y⁻¹ : Matrix n n R))
        (Set.range (fun ij : n × n => (Y : Matrix n n R) ij.1 ij.2))) = ⊤) :
    Function.Surjective (pvConstantMultiplication δB δ hδ) := by
  let μ := pvConstantMultiplication δB δ hδ
  let ι : R →ₐ[B] R ⊗[B] R := Algebra.TensorProduct.includeRight
  let K : Subalgebra B R := (μ.range.restrictScalars B).comap ι
  obtain ⟨hentries, hinverse⟩ :=
    pvConstantMultiplication_right_matrix_mem_range δB δ hδ A Y hY
  have hK : K = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro r hr
    rcases Set.mem_insert_iff.mp hr with hdet | hentry
    · subst r
      change ι (Matrix.det (↑Y⁻¹ : Matrix n n R)) ∈ μ.range
      rw [ι.map_det]
      apply matrix_det_mem_subalgebra
      exact hinverse
    · obtain ⟨⟨i,j⟩, rfl⟩ := hentry
      exact hentries i j
  have hright (r : R) : ι r ∈ μ.range := by
    change r ∈ K
    rw [hK]
    trivial
  intro z
  have hz : z ∈ μ.range := by
    induction z using TensorProduct.induction_on with
    | zero => exact μ.range.zero_mem
    | tmul r s =>
      have ht : r ⊗ₜ[B] s =
          (r ⊗ₜ[B] (1 : R)) * ((1 : R) ⊗ₜ[B] s) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht]
      exact μ.range.mul_mem (pvConstantMultiplication_left_mem_range δB δ hδ r) (hright s)
    | add x y hx hy => exact μ.range.add_mem hx hy
  exact hz
end Relative
end StrictEUnit

#print axioms StrictEUnit.matrix_det_mem_subalgebra
#print axioms StrictEUnit.pvConstantMultiplication_left_mem_range
#print axioms StrictEUnit.pvConstantMultiplication_constant_mem_range
#print axioms StrictEUnit.pvConstantMultiplication_right_matrix_mem_range
#print axioms StrictEUnit.pvConstantMultiplication_surjective
