import EulerCyclicJetTriangular
import ScalarEulerCompanionLogJets

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The scalar equation is constructed from the next ACTUAL row and the inverse
of the actual jet change. Its top coefficient is literally one. -/
def eulerCyclicScalarTuple {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K)) : Fin (n+2) →PowerSeries K :=
  Fin.lastCases 1 (fun j => -(∑ k,eulerCyclicRow C (n+1) k*(eulerCyclicJetMatrix C)⁻¹ k j))

@[simp] theorem eulerCyclicScalarTuple_top {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K)) :
    eulerCyclicScalarTuple C (Fin.last (n+1))=1 := by simp [eulerCyclicScalarTuple]

/-- Exact differential change-of-coordinates identity, in the power-series
ring. It includes the derivative of the change, not merely similarity. -/
theorem eulerCyclicCompanion_connection {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hG : IsUnit (eulerCyclicJetMatrix C).det) :
    (Matrix.of (fun i j =>powerSeriesEuler (eulerCyclicJetMatrix C i j)))+
      eulerCyclicJetMatrix C*C=
      scalarEulerPowerSeriesCompanion (n+1) (eulerCyclicScalarTuple C)*eulerCyclicJetMatrix C := by
  funext i j
  change powerSeriesEuler (eulerCyclicRow C i.val j)+
    (∑ k,eulerCyclicRow C i.val k*C k j)=_
  change eulerCyclicRow C (i.val+1) j=_
  by_cases hi : i.val+1<n+1
  · let k : Fin (n+1) := ⟨i.val+1,hi⟩
    have hk (l : Fin (n+1)) : l.val=i.val+1 ↔ l=k :=
      ⟨fun h =>Fin.ext h,fun h =>congrArg Fin.val h⟩
    simp only [Matrix.mul_apply,scalarEulerPowerSeriesCompanion,hi,if_true,hk,
      ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rfl
  · have hn : i.val+1=n+1 := by omega
    rw [hn]
    simp only [Matrix.mul_apply,scalarEulerPowerSeriesCompanion,hi,if_false,
      eulerCyclicScalarTuple,Fin.lastCases_last,Fin.lastCases_castSucc,inv_one,one_mul,neg_neg]
    simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    have hI := (eulerCyclicJetMatrix C).nonsing_inv_mul hG
    have he (k) : (∑ l,(eulerCyclicJetMatrix C)⁻¹ k l*eulerCyclicJetMatrix C l j)=
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K)) k j :=
      congrFun (congrFun hI k) j
    simp_rw [← Finset.mul_sum,he,Matrix.one_apply,mul_ite,mul_one,mul_zero]
    simp

/-- The inverse used for scalar jets really is a two-sided power-series inverse. -/
theorem eulerCyclicJetMatrix_inverse {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hC : ∀ i j,i.val+1<j.val → C i j=0)
    (hp : ∀ i : Fin n,IsUnit (C i.castSucc i.succ)) :
    eulerCyclicJetMatrix C*(eulerCyclicJetMatrix C)⁻¹=1 ∧
      (eulerCyclicJetMatrix C)⁻¹*eulerCyclicJetMatrix C=1 := by
  have h := eulerCyclicJetMatrix_det_isUnit C hC hp
  exact ⟨Matrix.mul_nonsing_inv _ h,Matrix.nonsing_inv_mul _ h⟩

end StrictEUnit
end
