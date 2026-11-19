import WeightedResidualParallelCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
section Packing
variable {K : Type*} [CommRing K]

/-- Finite forcing input, with the literal recursive newest-first ordering. -/
def finiteParallelVector {r : ℕ} (s : ℕ) (x : Fin r →K) (h : Fin s →K) : Fin (r+s) →K :=
  parallelForcingVector x (fun j =>if hj : j<s then h ⟨j,hj⟩ else 0) s

theorem finiteParallelVector_succ {r s : ℕ} (x : Fin r →K) (h : Fin (s+1) →K) :
    finiteParallelVector (s+1) x h=
      Fin.cases (h (Fin.last s)) (finiteParallelVector s x (fun j =>h j.castSucc)) := by
  funext i
  cases i using Fin.cases with
  | zero =>simp [finiteParallelVector,parallelForcingVector];rfl
  | succ i =>
    change parallelForcingVector x _ s i=parallelForcingVector x _ s i
    have he := (parallelForcingVector_eq_iff x x
      (fun j =>if hj : j<s+1 then h ⟨j,hj⟩ else 0)
      (fun j =>if hj : j<s then h (Fin.castSucc ⟨j,hj⟩) else 0) s).mpr
      ⟨rfl,fun j hj =>by simp [hj,Nat.lt_succ_of_lt hj]⟩
    exact congrFun he i

def finiteParallelLinear (r s : ℕ) : ((Fin r →K) × (Fin s →K)) →ₗ[K] (Fin (r+s) →K) where
  toFun := fun p =>finiteParallelVector s p.1 p.2
  map_add' := by
    intro p q
    induction s with
    | zero =>rfl
    | succ s ih =>
      simp only [finiteParallelVector_succ]
      funext i
      cases i using Fin.cases with
      | zero =>rfl
      | succ i =>exact congrFun (ih (p.1,fun j =>p.2 j.castSucc) (q.1,fun j =>q.2 j.castSucc)) i
  map_smul' := by
    intro a p
    induction s with
    | zero =>rfl
    | succ s ih =>
      simp only [finiteParallelVector_succ]
      funext i
      cases i using Fin.cases with
      | zero =>rfl
      | succ i =>exact congrFun (ih (p.1,fun j =>p.2 j.castSucc)) i

theorem finiteParallelLinear_bijective (r s : ℕ) : Function.Bijective (finiteParallelLinear (K:=K) r s) := by
  constructor
  · intro p q he
    have hh := (parallelForcingVector_eq_iff p.1 q.1 _ _ s).mp he
    apply Prod.ext hh.1
    funext j
    simpa only [dif_pos j.isLt] using hh.2 j.val j.isLt
  · intro v
    induction s with
    | zero =>exact ⟨(v,fun i =>Fin.elim0 i),rfl⟩
    | succ s ih =>
      obtain ⟨⟨x,h⟩,he⟩ := ih (fun i =>v i.succ)
      refine ⟨(x,Fin.lastCases (v 0) h),?_⟩
      change finiteParallelVector (s+1) x (Fin.lastCases (v 0) h)=v
      rw [finiteParallelVector_succ]
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
      change Fin.cases (v 0) (finiteParallelLinear r s (x,h))=v
      rw [he]
      funext i
      cases i using Fin.cases <;> rfl

def finiteParallelEquiv (r s : ℕ) : ((Fin r →K) × (Fin s →K)) ≃ₗ[K] (Fin (r+s) →K) :=
  LinearEquiv.ofBijective (finiteParallelLinear r s) (finiteParallelLinear_bijective r s)

end Packing
variable {K : Type*} [Field K] [CharZero K]

/-- Invertible moment transformation on the ENTIRE indexed coordinate space.
Source coordinates are unchanged; all forcing coordinates transform together. -/
def wholeSystemMomentGauge (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam) :
    (Fin (r+s) →K) ≃ₗ[K] (Fin (r+s) →K) :=
  ((finiteParallelEquiv r s).symm.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl K (Fin r →K))
      (Matrix.toLinearEquiv (Pi.basisFun K (Fin s)) (forcingMomentMatrix lam)
        (isUnit_iff_ne_zero.mpr (forcingMomentMatrix_det_ne_zero lam hlam))))).trans
    (finiteParallelEquiv r s)

theorem wholeSystemMomentGauge_apply (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam)
    (x : Fin r →K) (h : Fin s →K) :
    wholeSystemMomentGauge r s lam hlam (finiteParallelVector s x h)=
      finiteParallelVector s x ((forcingMomentMatrix lam).mulVec h) := by
  change (finiteParallelEquiv r s)
    ((LinearEquiv.prodCongr (LinearEquiv.refl K (Fin r →K))
      (Matrix.toLinearEquiv (Pi.basisFun K (Fin s)) (forcingMomentMatrix lam) _))
      ((finiteParallelEquiv r s).symm ((finiteParallelEquiv r s) (x,h))))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

end StrictEUnit
end
