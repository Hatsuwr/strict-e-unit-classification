import OrderedMomentCyclicFrame

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {R : Type*} [CommRing R]

def orderedParallelEquiv (r s : ℕ) : ((Fin r →R) × (Fin s →R)) ≃ₗ[R] (Fin (r+s) →R) where
  toFun p := Fin.addCases p.1 p.2
  invFun v := (fun i =>v (Fin.castAdd s i),fun j =>v (Fin.natAdd r j))
  left_inv p := by ext i <;> simp
  right_inv v := by funext i;cases i using Fin.addCases <;> simp
  map_add' p q := by funext i;cases i using Fin.addCases <;> simp
  map_smul' a p := by funext i;cases i using Fin.addCases <;> simp

def orderedSystemGauge (r s : ℕ) (V : Matrix (Fin s) (Fin s) R) (hV : IsUnit V.det) :
    (Fin (r+s) →R) ≃ₗ[R] (Fin (r+s) →R) :=
  ((finiteParallelEquiv r s).symm.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl R (Fin r →R))
      (Matrix.toLinearEquiv (Pi.basisFun R (Fin s)) V hV))).trans (orderedParallelEquiv r s)

theorem orderedSystemGauge_apply (r s : ℕ) (V : Matrix (Fin s) (Fin s) R) (hV : IsUnit V.det)
    (x : Fin r →R) (h : Fin s →R) :
    orderedSystemGauge r s V hV (finiteParallelVector s x h)=Fin.addCases x (V.mulVec h) := by
  change (orderedParallelEquiv r s)
    ((LinearEquiv.prodCongr (LinearEquiv.refl R (Fin r →R))
      (Matrix.toLinearEquiv (Pi.basisFun R (Fin s)) V hV))
      ((finiteParallelEquiv r s).symm ((finiteParallelEquiv r s) (x,h))))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem orderedMomentConnection_action {r s : ℕ}
    (C : Matrix (Fin r) (Fin r) R) (g : Fin r →R) (a : Fin (s+1) →R)
    (x : Fin r →R) (h : Fin (s+1) →R) :
    (orderedMomentConnection C g a).mulVec (Fin.addCases x h)=
      Fin.addCases (fun i =>C.mulVec x i+g i*h 0)
        ((Matrix.of (fun i =>Fin.lastCases a (fun j =>fun k =>if k=j.succ then 1 else 0) i)).mulVec h) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    change (∑ j,orderedMomentConnection C g a (Fin.castAdd (s+1) i) j*Fin.addCases x h j)=_
    rw [Fin.sum_univ_add]
    simp only [orderedMomentConnection,Fin.addCases_left,Fin.addCases_right,ite_mul,zero_mul]
    have he : (∑ j : Fin (s+1),if j.val=0 then g i*h j else 0)=g i*h 0 := by
      have hh (j : Fin (s+1)) : j.val=0 ↔ j=0 := by constructor; exact fun h =>Fin.ext h; exact fun h =>congrArg Fin.val h
      simp only [hh]
      simp
    rw [he]
    rfl
  | right i =>
    change (∑ j,orderedMomentConnection C g a (Fin.natAdd r i) j*Fin.addCases x h j)=_
    rw [Fin.sum_univ_add]
    simp only [orderedMomentConnection,Fin.addCases_left,Fin.addCases_right,zero_mul,
      Finset.sum_const_zero,zero_add]
    rfl

end StrictEUnit
end
