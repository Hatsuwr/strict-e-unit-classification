import FormalPolynomialImage
import FormalCandidateCoaction
import MatrixGeneratedChangeBasis

/-! Actual logarithm removal for matrices whose entries belong to the Laurent
series coefficient field. The matrix and any base-unit change of basis are
supplied. No existence, convergence, or analytic interpretation is asserted. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit
variable {k : Type*} [Field k]
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
/-- Transport along a proved equality of actual subalgebras. -/
theorem formalPolynomial_unit_of_image_eq {L : Type*} [Field L] [Algebra k L]
    (S : Subalgebra k L) (R : Subalgebra k (RatFunc L))
    (h : R = (formalPolynomialEmbedding S).range) (u : R) (hu : IsUnit u) :
    ∃ s : S, IsUnit s ∧ RatFunc.C (s : L) = (u : RatFunc L) := by
  subst R
  exact formalPolynomialImage_unit_is_coefficient S u hu

variable {n : Type*} [Fintype n] [DecidableEq n]

def formalMatrixCoefficientAlgebra (F : Matrix n n (LaurentSeries k)) :
    Subalgebra k (LaurentSeries k) :=
  Algebra.adjoin k (Set.range (laurentPolynomialToSeries (k := k)) ∪
    insert F.det⁻¹ (Set.range fun ij : n × n => F ij.1 ij.2))

@[simp] theorem formalBaseEmbedding_C (p : LaurentPolynomial k) :
    formalBaseEmbedding (Polynomial.C p) = RatFunc.C (laurentPolynomialToSeries p) := by
  change algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
    ((Polynomial.C p).map laurentPolynomialToSeries.toRingHom) = _
  simp

@[simp] theorem formalBaseEmbedding_X :
    formalBaseEmbedding (Polynomial.X : LaurentLogBase k) = RatFunc.X := by
  change algebraMap (Polynomial (LaurentSeries k)) (RatFunc (LaurentSeries k))
    (Polynomial.X.map laurentPolynomialToSeries.toRingHom) = _
  simp

theorem formalMatrix_base_mem_image (F : Matrix n n (LaurentSeries k))
    (p : LaurentLogBase k) :
    formalBaseEmbedding p ∈ (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using Subalgebra.add_mem _ hp hq
  | monomial j a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      formalBaseEmbedding_C, formalBaseEmbedding_X]
    apply Subalgebra.mul_mem
    · exact ⟨Polynomial.C ⟨laurentPolynomialToSeries a,
        Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)⟩,
        formalPolynomialEmbedding_C _ _⟩
    · exact Subalgebra.pow_mem (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range
        ⟨Polynomial.X, formalPolynomialEmbedding_X _⟩ j

theorem formalMatrix_coefficient_mem_candidate (F : Matrix n n (LaurentSeries k))
    (s : LaurentSeries k) (hs : s ∈ formalMatrixCoefficientAlgebra F) :
    RatFunc.C s ∈ matrixGeneratedAlgebra (B := LaurentLogBase k) (F.map RatFunc.C) := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | (rfl | ⟨⟨i,j⟩, rfl⟩)
    · rw [← formalBaseEmbedding_C]
      exact (matrixGeneratedAlgebra _).algebraMap_mem (Polynomial.C a)
    · have hd : RatFunc.C F.det⁻¹ = (F.map RatFunc.C).det⁻¹ := by
        rw [map_inv₀, RingHom.map_det]; rfl
      rw [hd]
      exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · exact matrixEntryAlgebra_le _ (matrixEntry_mem _ i j)
  | algebraMap a =>
    have ha : RatFunc.C (algebraMap k (LaurentSeries k) a) =
        algebraMap k (RatFunc (LaurentSeries k)) a := by
      rw [RatFunc.algebraMap_apply, map_one, div_one]
      rfl
    rw [ha]
    exact ((matrixGeneratedAlgebra (B := LaurentLogBase k) (F.map RatFunc.C)).restrictScalars k).algebraMap_mem a
  | add x y hx hy ihx ihy => rw [RatFunc.C.map_add x y]; exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy => rw [RatFunc.C.map_mul x y]; exact Subalgebra.mul_mem _ ihx ihy

theorem formalMatrix_candidate_eq_polynomial_image (F : Matrix n n (LaurentSeries k)) :
    (matrixGeneratedAlgebra (B := LaurentLogBase k) (F.map RatFunc.C)).restrictScalars k =
      (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range := by
  apply le_antisymm
  · let T : Subalgebra (LaurentLogBase k) (RatFunc (LaurentSeries k)) :=
      { (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range.toSubsemiring with
        algebraMap_mem' := formalMatrix_base_mem_image F }
    have h : matrixGeneratedAlgebra (B := LaurentLogBase k) (F.map RatFunc.C) ≤ T := by
      apply (matrixGeneratedAlgebra_le_iff _ _).mpr
      constructor
      · change (F.map RatFunc.C).det⁻¹ ∈ (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range
        have hd : (F.map RatFunc.C).det⁻¹ = RatFunc.C F.det⁻¹ := by
          rw [map_inv₀, RingHom.map_det]; rfl
        rw [hd]
        exact ⟨Polynomial.C ⟨F.det⁻¹, Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))⟩,
          formalPolynomialEmbedding_C _ _⟩
      · intro i j
        change RatFunc.C (F i j) ∈ (formalPolynomialEmbedding (formalMatrixCoefficientAlgebra F)).range
        exact ⟨Polynomial.C ⟨F i j, Algebra.subset_adjoin
          (Or.inr (Set.mem_insert_of_mem _ ⟨(i,j), rfl⟩))⟩,
          formalPolynomialEmbedding_C _ _⟩
    exact h
  · rw [formalPolynomialEmbedding_range, Algebra.adjoin_le_iff]
    rintro x (rfl | ⟨s, hs, rfl⟩)
    · rw [← formalBaseEmbedding_X]
      exact (matrixGeneratedAlgebra _).algebraMap_mem Polynomial.X
    · exact formalMatrix_coefficient_mem_candidate F s hs

/-- Every unit in the actual matrix-generated algebra is log-free. -/
theorem formalMatrix_unit_is_coefficient (F : Matrix n n (LaurentSeries k))
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k) (F.map RatFunc.C))
    (hu : IsUnit u) :
    ∃ s : formalMatrixCoefficientAlgebra F, IsUnit s ∧
      RatFunc.C (s : LaurentSeries k) = (u : RatFunc (LaurentSeries k)) := by
  exact formalPolynomial_unit_of_image_eq _ _
    (formalMatrix_candidate_eq_polynomial_image F) u hu

/-- A supplied invertible base change does not alter the log-removal result. -/
theorem formalMatrix_base_change_unit_is_coefficient (F : Matrix n n (LaurentSeries k))
    (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (u : matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))))
    (hu : IsUnit u) :
    ∃ s : formalMatrixCoefficientAlgebra F, IsUnit s ∧
      RatFunc.C (s : LaurentSeries k) = (u : RatFunc (LaurentSeries k)) := by
  apply formalPolynomial_unit_of_image_eq (formalMatrixCoefficientAlgebra F)
    ((matrixGeneratedAlgebra (B := LaurentLogBase k)
      ((F.map RatFunc.C) * (Z : Matrix n n (LaurentLogBase k)).map
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))).restrictScalars k) _ u hu
  rw [matrixGeneratedAlgebra_mul_base_unit]
  exact formalMatrix_candidate_eq_polynomial_image F

end StrictEUnit
#print axioms StrictEUnit.formalMatrixCoefficientAlgebra
#print axioms StrictEUnit.formalBaseEmbedding_C
#print axioms StrictEUnit.formalBaseEmbedding_X
#print axioms StrictEUnit.formalMatrix_base_mem_image
#print axioms StrictEUnit.formalMatrix_coefficient_mem_candidate
#print axioms StrictEUnit.formalMatrix_candidate_eq_polynomial_image

#print axioms StrictEUnit.formalMatrix_unit_is_coefficient
#print axioms StrictEUnit.formalMatrix_base_change_unit_is_coefficient

#print axioms StrictEUnit.formalPolynomial_unit_of_image_eq
