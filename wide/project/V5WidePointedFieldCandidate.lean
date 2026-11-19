import V5WidePointedCandidate
import MatrixGeneratedDifferentialAlgebra

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instSMul
namespace StrictEUnit
variable {K : Type*} [Field K] {r : ℕ}

instance v5WidePointedLaurentAlgebra : Algebra (LaurentPolynomial K) (LaurentSeries K) :=
  (v5WidePointedLaurentBase K).toRingHom.toAlgebra

instance v5WidePointedLaurentTower :
    IsScalarTower K (LaurentPolynomial K) (LaurentSeries K) :=
  IsScalarTower.of_algebraMap_eq' (v5WidePointedLaurentBase K).comp_algebraMap.symm

def v5WidePowerSeriesInclusion : PowerSeries K →ₐ[K] LaurentSeries K :=
  { HahnSeries.ofPowerSeries ℤ K with commutes' := fun _ => rfl }

abbrev V5WideFieldCandidate (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :=
  matrixGeneratedAlgebra (B := LaurentPolynomial K) (v5WidePointedLaurentFundamental A)

theorem v5WidePointed_inverse_det_map
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    v5WidePowerSeriesInclusion ((v5WidePointedFundamental A).det⁻¹) =
      (v5WidePointedLaurentFundamental A).det⁻¹ := by
  have h : (v5WidePowerSeriesInclusion (K := K)) (v5WidePointedFundamental A).det *
      v5WidePowerSeriesInclusion ((v5WidePointedFundamental A).det⁻¹) = 1 := by
    rw [← map_mul]
    rw [PowerSeries.mul_inv_cancel _ (by rw [v5WidePointedFundamental_det_constant]; exact one_ne_zero), map_one]
  rw [AlgHom.map_det] at h
  exact eq_inv_of_mul_eq_one_right h

theorem v5WidePointed_map_mem (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))
    (x : v5WidePointedCandidate A) :
    v5WidePowerSeriesInclusion x.val ∈ V5WideFieldCandidate A := by
  rcases x with ⟨x,hx⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with (⟨p,rfl⟩ | ⟨⟨i,j⟩,rfl⟩) | rfl
    · exact (V5WideFieldCandidate A).algebraMap_mem p
    · exact Algebra.subset_adjoin (Or.inr ⟨(i,j),rfl⟩)
    · rw [v5WidePointed_inverse_det_map]
      exact Algebra.subset_adjoin (Or.inl rfl)
  | algebraMap c =>
    rw [(v5WidePowerSeriesInclusion (K := K)).commutes]
    exact ((V5WideFieldCandidate A).restrictScalars K).algebraMap_mem c
  | add x y hx hy ihx ihy => simpa only [map_add] using (V5WideFieldCandidate A).add_mem ihx ihy
  | mul x y hx hy ihx ihy => simpa only [map_mul] using (V5WideFieldCandidate A).mul_mem ihx ihy

def v5WidePointedFieldMap (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    v5WidePointedCandidate A →ₐ[K] V5WideFieldCandidate A :=
  ((v5WidePowerSeriesInclusion (K := K)).comp (v5WidePointedCandidate A).val).codRestrict
    ((V5WideFieldCandidate A).restrictScalars K) (v5WidePointed_map_mem A)

theorem v5WidePointedFieldMap_injective
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Function.Injective (v5WidePointedFieldMap A) := by
  intro x y h
  apply Subtype.ext
  exact HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h)

theorem v5WidePointedFieldMap_surjective
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Function.Surjective (v5WidePointedFieldMap A) := by
  rintro ⟨x,hx⟩
  change x ∈ Algebra.adjoin (LaurentPolynomial K) _ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨⟨i,j⟩,rfl⟩
    · refine ⟨⟨_,v5WidePointedCandidate_inverse_det_mem A⟩, ?_⟩
      apply Subtype.ext
      exact v5WidePointed_inverse_det_map A
    · exact ⟨⟨_,v5WidePointedCandidate_entry_mem A i j⟩,rfl⟩
  | algebraMap p => exact ⟨v5WidePointedCandidateBase A p,rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a,ha⟩ := ihx
    obtain ⟨b,hb⟩ := ihy
    exact ⟨a+b, by rw [map_add,ha,hb]; rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a,ha⟩ := ihx
    obtain ⟨b,hb⟩ := ihy
    exact ⟨a*b, by rw [map_mul,ha,hb]; rfl⟩

def v5WidePointedFieldEquiv (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    v5WidePointedCandidate A ≃ₐ[K] V5WideFieldCandidate A :=
  AlgEquiv.ofBijective (v5WidePointedFieldMap A)
    ⟨v5WidePointedFieldMap_injective A,v5WidePointedFieldMap_surjective A⟩

def v5WideFieldCandidatePoint (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    V5WideFieldCandidate A →ₐ[K] K :=
  (v5WidePointedCandidatePoint A).comp (v5WidePointedFieldEquiv A).symm.toAlgHom

@[simp] theorem v5WideFieldCandidatePoint_base
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) (p : LaurentPolynomial K) :
    v5WideFieldCandidatePoint A (algebraMap (LaurentPolynomial K) (V5WideFieldCandidate A) p) =
      LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) p := by
  have h : algebraMap (LaurentPolynomial K) (V5WideFieldCandidate A) p =
      v5WidePointedFieldEquiv A (v5WidePointedCandidateBase A p) := rfl
  rw [h]
  change v5WidePointedCandidatePoint A
    ((v5WidePointedFieldEquiv A).symm ((v5WidePointedFieldEquiv A) _)) = _
  rw [AlgEquiv.symm_apply_apply, v5WidePointedCandidatePoint_base]

def v5WideFieldCandidateMatrix
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    Matrix (Fin r) (Fin r) (V5WideFieldCandidate A) :=
  (v5WidePointedCandidateMatrix A).map (v5WidePointedFieldEquiv A)

@[simp] theorem v5WideFieldCandidateMatrix_val
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) (i j : Fin r) :
    (v5WideFieldCandidateMatrix A i j).val = v5WidePointedLaurentFundamental A i j := rfl

theorem v5WideFieldCandidateMatrix_isUnit
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    IsUnit (v5WideFieldCandidateMatrix A) :=
  (v5WidePointedCandidateMatrix_isUnit A).map (v5WidePointedFieldEquiv A).toRingEquiv.toRingHom.mapMatrix

@[simp] theorem v5WideFieldCandidateMatrix_normalized
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (v5WideFieldCandidateMatrix A).map (v5WideFieldCandidatePoint A) = 1 := by
  have h := v5WidePointedCandidateMatrix_normalized A
  ext i j
  change v5WidePointedCandidatePoint A
    ((v5WidePointedFieldEquiv A).symm ((v5WidePointedFieldEquiv A)
      (v5WidePointedCandidateMatrix A i j))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact congrArg (fun M => M i j) h

end StrictEUnit
#print axioms StrictEUnit.v5WidePointedFieldEquiv
#print axioms StrictEUnit.v5WideFieldCandidatePoint

#print axioms StrictEUnit.v5WideFieldCandidatePoint_base

#print axioms StrictEUnit.v5WideFieldCandidateMatrix_isUnit
#print axioms StrictEUnit.v5WideFieldCandidateMatrix_normalized
