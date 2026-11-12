import OrderedMomentGaugeAction

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem finiteLaurentEulerMatrix_finite_action {r s : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ) (x : Fin r →PowerSeries K) (h : Fin s →PowerSeries K) :
    (finiteLaurentEulerMatrix C g M k s).mulVec (finiteParallelVector s x h)=
      finiteParallelVector s (fun i =>C.mulVec x i+g i*∑ j,h j)
        (fun j =>PowerSeries.C K (((M:ℤ)+k j.val):K)*h j) := by
  unfold finiteParallelVector
  rw [finiteLaurentEulerMatrix_mul_parallel]
  apply (parallelForcingVector_eq_iff _ _ _ _ s).mpr
  constructor
  · funext i
    congr 1
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [dif_pos j.isLt]
  · intro j hj
    simp [hj]

theorem mappedMoment_zeroth {s : ℕ} (lam : Fin (s+1) →K) (h : Fin (s+1) →PowerSeries K) :
    (((forcingMomentMatrix lam).map (PowerSeries.C K)).mulVec h) 0=∑ j,h j := by
  simp [Matrix.mulVec,dotProduct,forcingMomentMatrix,Matrix.vandermonde_apply]

/-- The literal recursively indexed matrix intertwines with the explicit
source-first moment companion system on EVERY vector, not only solutions. -/
theorem actualOrderedMoment_intertwines {r s : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ) (lam a : Fin (s+1) →K)
    (hlam : ∀ j,lam j=(((M:ℤ)+k j.val):K))
    (ha : ∀ j,lam j^(s+1)=∑ m : Fin (s+1),a m*lam j^m.val)
    (hV : IsUnit (((forcingMomentMatrix lam).map (PowerSeries.C K)).det))
    (v : Fin (r+(s+1)) →PowerSeries K) :
    orderedSystemGauge r (s+1) ((forcingMomentMatrix lam).map (PowerSeries.C K)) hV
      ((finiteLaurentEulerMatrix C g M k (s+1)).mulVec v)=
      (orderedMomentConnection C g (fun j =>PowerSeries.C K (a j))).mulVec
        (orderedSystemGauge r (s+1) ((forcingMomentMatrix lam).map (PowerSeries.C K)) hV v) := by
  obtain ⟨⟨x,h⟩,he⟩ := (finiteParallelLinear_bijective (K:=PowerSeries K) r (s+1)).2 v
  change finiteParallelVector (s+1) x h=v at he
  rw [← he,finiteLaurentEulerMatrix_finite_action,orderedSystemGauge_apply,
    orderedSystemGauge_apply,orderedMomentConnection_action,mappedMoment_zeroth]
  have hd : (fun j : Fin (s+1) =>PowerSeries.C K (((M:ℤ)+k j.val):K)*h j)=
      ((Matrix.diagonal lam).map (PowerSeries.C K)).mulVec h := by
    funext j
    simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,hlam,apply_ite,ite_mul]
  have hh : ((forcingMomentMatrix lam).map (PowerSeries.C K)).mulVec
      (fun j =>PowerSeries.C K (((M:ℤ)+k j.val):K)*h j)=
      ((parallelMomentCompanion a).map (PowerSeries.C K)).mulVec
        (((forcingMomentMatrix lam).map (PowerSeries.C K)).mulVec h) := by
    rw [hd,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    apply congrArg (fun A : Matrix (Fin (s+1)) (Fin (s+1)) (PowerSeries K) =>A.mulVec h)
    change (PowerSeries.C K).mapMatrix _*(PowerSeries.C K).mapMatrix _=
      (PowerSeries.C K).mapMatrix _*(PowerSeries.C K).mapMatrix _
    rw [← map_mul,← map_mul,forcingMomentMatrix_intertwines lam a ha]
  have hm : (parallelMomentCompanion a).map (PowerSeries.C K)=
      Matrix.of (fun i =>Fin.lastCases (fun j =>PowerSeries.C K (a j))
        (fun j =>fun k =>if k=j.succ then 1 else 0) i) := by
    funext i j
    cases i using Fin.lastCases <;> simp [parallelMomentCompanion,Matrix.map_apply,apply_ite]
  rw [hh,hm]

end StrictEUnit
end
