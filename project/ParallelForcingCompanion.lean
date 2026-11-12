import ParallelForcingMoments

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Interpolation supplies the final companion row over the SAME field. -/
theorem forcingMoment_closure_coefficients {s : ℕ} (lam : Fin s → K)
    (hlam : Function.Injective lam) :
    ∃ a : Fin s → K, ∀ j,lam j^s=∑ m : Fin s,a m*lam j^m.val := by
  let V := Matrix.vandermonde lam
  have hu : IsUnit V := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hlam))
  obtain ⟨a,ha⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) (fun j =>lam j^s)
  refine ⟨a,fun j =>?_⟩
  have hj := congrFun ha j
  simpa only [Matrix.mulVec, dotProduct, V,Matrix.vandermonde_apply,mul_comm] using hj.symm

def parallelMomentCompanion {n : ℕ} (a : Fin (n+1) → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  fun i =>Fin.lastCases a (fun j =>fun k =>if k=j.succ then 1 else 0) i

/-- Exact diagonal-to-companion intertwining, before any differential or
arithmetic transport. -/
theorem forcingMomentMatrix_intertwines {n : ℕ} (lam a : Fin (n+1) → K)
    (ha : ∀ j,lam j^(n+1)=∑ m : Fin (n+1),a m*lam j^m.val) :
    forcingMomentMatrix lam * Matrix.diagonal lam =
      parallelMomentCompanion a * forcingMomentMatrix lam := by
  ext i j
  rw [Matrix.mul_diagonal]
  cases i using Fin.lastCases with
  | last =>
    simpa only [forcingMomentMatrix,Matrix.transpose_apply,Matrix.vandermonde_apply,
      Fin.val_last,pow_succ,Matrix.mul_apply,parallelMomentCompanion,Fin.lastCases_last] using ha j
  | cast i =>
    simp only [Matrix.mul_apply,parallelMomentCompanion,Fin.lastCases_castSucc]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
      forcingMomentMatrix,Matrix.transpose_apply,Matrix.vandermonde_apply,
      Fin.coe_castSucc,Fin.val_succ,pow_succ]

end StrictEUnit
end
