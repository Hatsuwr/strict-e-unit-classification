import V5WidePointedFundamental

noncomputable section
open scoped Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] {r : ℕ}

/-- The explicit ordinary-point candidate: the supplied Laurent coefficients,
entries of the constructed fundamental matrix, and inverse determinant.
This definition alone does not assert the PV torsor or comparison theorem. -/
def v5WidePointedCandidate
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) : Subalgebra K (PowerSeries K) :=
  Algebra.adjoin K (Set.range (v5WidePointedBase K) ∪
    Set.range (fun ij : Fin r × Fin r => v5WidePointedFundamental A ij.1 ij.2) ∪
    {(v5WidePointedFundamental A).det⁻¹})

theorem v5WidePointedCandidate_base_mem
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) (p : LaurentPolynomial K) :
    v5WidePointedBase K p ∈ v5WidePointedCandidate A :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨p,rfl⟩))

theorem v5WidePointedCandidate_entry_mem
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) (i j : Fin r) :
    v5WidePointedFundamental A i j ∈ v5WidePointedCandidate A :=
  Algebra.subset_adjoin (Or.inl (Or.inr ⟨(i,j),rfl⟩))

theorem v5WidePointedCandidate_inverse_det_mem
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (v5WidePointedFundamental A).det⁻¹ ∈ v5WidePointedCandidate A :=
  Algebra.subset_adjoin (Or.inr rfl)

/-- The actual base inclusion in the pointed candidate, with no quotient. -/
def v5WidePointedCandidateBase
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    LaurentPolynomial K →ₐ[K] v5WidePointedCandidate A :=
  (v5WidePointedBase K).codRestrict _ (v5WidePointedCandidate_base_mem A)

theorem v5WidePointedCandidateBase_injective
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Function.Injective (v5WidePointedCandidateBase A) := by
  intro p q h
  exact v5WidePointedBase_injective K (congrArg Subtype.val h)

/-- Evaluation at the fixed ordinary point, defined over K itself. -/
def v5WidePointedCandidatePoint
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    v5WidePointedCandidate A →ₐ[K] K :=
  { (PowerSeries.constantCoeff K).comp (v5WidePointedCandidate A).val.toRingHom with
    commutes' := by intro c; exact PowerSeries.constantCoeff_C c }

@[simp] theorem v5WidePointedCandidatePoint_base
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) (p : LaurentPolynomial K) :
    v5WidePointedCandidatePoint A (v5WidePointedCandidateBase A p) =
      LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) p :=
  v5WidePointedBase_constant K p

/-- The fundamental matrix, with its entries in the candidate itself. -/
def v5WidePointedCandidateMatrix
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Matrix (Fin r) (Fin r) (v5WidePointedCandidate A) :=
  fun i j => ⟨v5WidePointedFundamental A i j,v5WidePointedCandidate_entry_mem A i j⟩

@[simp] theorem v5WidePointedCandidateMatrix_normalized
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (v5WidePointedCandidateMatrix A).map (v5WidePointedCandidatePoint A) = 1 :=
  v5WidePointedFundamental_normalized A

theorem v5WidePointedCandidateMatrix_isUnit
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    IsUnit (v5WidePointedCandidateMatrix A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_exists_inv.2
  refine ⟨⟨(v5WidePointedFundamental A).det⁻¹,
    v5WidePointedCandidate_inverse_det_mem A⟩, ?_⟩
  apply Subtype.ext
  change (v5WidePointedCandidate A).val ((v5WidePointedCandidateMatrix A).det) *
    (v5WidePointedFundamental A).det⁻¹ = 1
  rw [AlgHom.map_det]
  change (v5WidePointedFundamental A).det * (v5WidePointedFundamental A).det⁻¹ = 1
  apply PowerSeries.mul_inv_cancel
  rw [v5WidePointedFundamental_det_constant]
  exact one_ne_zero

#print axioms v5WidePointedCandidateBase_injective
#print axioms v5WidePointedCandidatePoint_base
#print axioms v5WidePointedCandidateMatrix_isUnit
end StrictEUnit
