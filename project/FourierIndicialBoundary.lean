import FourierIndicialTwistedAmplitudes

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The actual critical diagonal of the SAME unnormalized Fourier array. -/
def fourierBoundaryIndicial {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) : Polynomial K :=
  ∑ i,∑ j,if stage57_exponent i j=0 then
    Polynomial.C ((-1:K)^j.val*A i j)*stage61_shiftedDesc i.val j.val else 0

theorem fourierBoundaryIndicial_natDegree_le {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : (fourierBoundaryIndicial A).natDegree ≤ ν := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  split_ifs
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((stage61_shiftedDesc_natDegree i.val j.val).le.trans (Nat.le_of_lt_succ j.isLt))
  · simp

/-- Extraction of the literal regular lift gives exactly the critical-diagonal
polynomial. No corner normalization or source-spectrum premise is supplied. -/
theorem sameFourierEulerIndicial_eq_boundary {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A) :
    sameFourierEulerCoefficientSymbols A hf 0=fourierBoundaryIndicial A := by
  classical
  have hleft : (sameFourierEulerCoefficientSymbols A hf 0).natDegree ≤ ν := by
    unfold sameFourierEulerCoefficientSymbols scalarEulerCoefficientSymbol
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)
  apply (Polynomial.ext_iff_natDegree_le hleft (fourierBoundaryIndicial_natDegree_le A)).2
  intro k hk
  let i : Fin (ν+1) := ⟨k,Nat.lt_succ_of_le hk⟩
  have hcoeff : (sameFourierEulerCoefficientSymbols A hf 0).coeff k=
      PowerSeries.coeff K 0 ((stage61_fourierLift A hf).coeff k) :=
    scalarEulerCoefficientSymbol_coeff_fin ν _ 0 i
  rw [hcoeff]
  have h := congrArg (fun f : LaurentSeries K => f.coeff (0:ℤ))
    (stage59_regularLift_map_coeff (stage61_fourierEulerSymbol A)
      (stage61_fourierEulerSymbol_regular A hf) k)
  dsimp only at h
  change (HahnSeries.ofPowerSeries ℤ K
    ((stage59_regularLift (stage61_fourierEulerSymbol A)
      (stage61_fourierEulerSymbol_regular A hf)).coeff k)).coeff ((0:ℕ):ℤ)=_ at h
  rw [HahnSeries.ofPowerSeries_apply_coeff] at h
  change PowerSeries.coeff K 0 ((stage61_fourierLift A hf).coeff k)=_ at h
  rw [h,stage61_fourierEulerSymbol_coeff]
  simp only [HahnSeries.coeff_sum,fourierBoundaryIndicial,Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases he : stage57_exponent u v=0
  · rw [if_pos he,Polynomial.coeff_C_mul,he,HahnSeries.coeff_single_same]
  · rw [if_neg he,Polynomial.coeff_zero,HahnSeries.coeff_single_of_ne (Ne.symm he)]

end StrictEUnit
end
