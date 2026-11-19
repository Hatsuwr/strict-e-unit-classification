import AugmentedSourceEulerMatrix
import EulerCyclicJetTriangular

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

/-- Reorder a newly prepended forcing coordinate after all previous coordinates. -/
def appendCoordinateEquiv {r : ℕ} (e : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) where
  toFun := Fin.lastCases 0 (fun i =>(e i).succ)
  invFun := Fin.cases (Fin.last r) (fun i =>(e.symm i).castSucc)
  left_inv i := by cases i using Fin.lastCases <;> simp
  right_inv i := by cases i using Fin.cases <;> simp

@[simp] theorem appendCoordinateEquiv_last {r : ℕ} (e : Equiv.Perm (Fin r)) :
    appendCoordinateEquiv e (Fin.last r)=0 := by simp [appendCoordinateEquiv]
@[simp] theorem appendCoordinateEquiv_castSucc {r : ℕ} (e : Equiv.Perm (Fin r)) (i : Fin r) :
    appendCoordinateEquiv e i.castSucc=(e i).succ := by simp [appendCoordinateEquiv]

def appendEulerBlock {R : Type*} [Zero R] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) R) (g : Fin r →R) (u : R) :
    Matrix (Fin (r+1)) (Fin (r+1)) R :=
  Fin.lastCases (Fin.lastCases u (fun _ =>0)) (fun i =>Fin.lastCases (g i) (C i))

theorem forcingEulerBlock_reindex {R : Type*} [Zero R] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) R) (g : Fin r →R) (u : R) (e : Equiv.Perm (Fin r)) :
    (forcingEulerBlock C g u).submatrix (appendCoordinateEquiv e) (appendCoordinateEquiv e)=
      appendEulerBlock (C.submatrix e e) (fun i =>g (e i)) u := by
  funext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [Matrix.submatrix,forcingEulerBlock,appendEulerBlock]

/-- Source jets first, then forcing derivatives in increasing order. -/
def forcingCoordinateEquiv (r : ℕ) : (d : ℕ) →Equiv.Perm (Fin ((r+1)+d))
  | 0 =>appendCoordinateEquiv (Equiv.refl _)
  | d+1 =>appendCoordinateEquiv (forcingCoordinateEquiv r d)

@[simp] theorem forcingCoordinateEquiv_last (r d : ℕ) :
    forcingCoordinateEquiv r d ⟨r+d,by omega⟩=0 := by
  cases d with
  | zero =>exact appendCoordinateEquiv_last (Equiv.refl (Fin r))
  | succ d =>
    have h : (⟨r+(d+1),by omega⟩ : Fin ((r+1)+(d+1)))=Fin.last ((r+1)+d) := Fin.ext (by simp;omega)
    rw [h,forcingCoordinateEquiv]
    exact appendCoordinateEquiv_last (forcingCoordinateEquiv r d)

variable {K : Type*} [Field K]

def orderedForcingEulerMatrix {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K) (u : ℕ) :
    (d : ℕ) →Matrix (Fin ((r+1)+d)) (Fin ((r+1)+d)) (PowerSeries K)
  | 0 =>appendEulerBlock C g (PowerSeries.C K (u : K))
  | d+1 =>appendEulerBlock (orderedForcingEulerMatrix C g u d)
      (fun i =>if i.val+1=(r+1)+d then 1 else 0) (PowerSeries.C K ((u+d+1 : ℕ) : K))

/-- Exact permutation of the previously constructed forcing matrix. -/
theorem polynomialForcingEulerMatrix_ordered {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K) (u d : ℕ) :
    (polynomialForcingEulerMatrix C g u d).submatrix (forcingCoordinateEquiv r d)
      (forcingCoordinateEquiv r d)=orderedForcingEulerMatrix C g u d := by
  induction d with
  | zero =>simpa [polynomialForcingEulerMatrix,forcingCoordinateEquiv,orderedForcingEulerMatrix] using
      forcingEulerBlock_reindex C g (PowerSeries.C K (u : K)) (Equiv.refl _)
  | succ d ih =>
    rw [polynomialForcingEulerMatrix,forcingCoordinateEquiv]
    refine (forcingEulerBlock_reindex (polynomialForcingEulerMatrix C g u d)
      (fun i =>if i.val=0 then 1 else 0) (PowerSeries.C K ((u+d+1 : ℕ) : K))
      (forcingCoordinateEquiv r d)).trans ?_
    rw [ih]
    change appendEulerBlock _ _ _=appendEulerBlock _ _ _
    have hg : (fun i : Fin ((r+1)+d) =>if (forcingCoordinateEquiv r d i).val=0 then (1 : PowerSeries K) else 0)=
        (fun i =>if i.val+1=(r+1)+d then 1 else 0) := by
      funext i
      have h : (forcingCoordinateEquiv r d i).val=0 ↔ i.val+1=(r+1)+d := by
        constructor
        · intro hi
          have he : forcingCoordinateEquiv r d i=0 := Fin.ext hi
          have hi' : i=⟨r+d,by omega⟩ := (forcingCoordinateEquiv r d).injective
            (he.trans (forcingCoordinateEquiv_last r d).symm)
          have hv := congrArg Fin.val hi'
          simp only [Fin.val_mk] at hv
          omega
        · intro hi
          have hi' : i=⟨r+d,by omega⟩ := Fin.ext (by simp;omega)
          rw [hi',forcingCoordinateEquiv_last];rfl
      simp only [h]
    rw [hg]
    rfl


/-- A support/pivot criterion, including the actual unit superdiagonal. -/
def EulerCyclicShape {R : Type*} [CommRing R] {r : ℕ} (C : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ i j,i.val+1<j.val → C i j=0) ∧
    ∀ i j,j.val=i.val+1 → IsUnit (C i j)

theorem appendEulerBlock_cyclicShape {R : Type*} [CommRing R] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) R) (g : Fin r →R) (u : R)
    (hC : EulerCyclicShape C)
    (hg0 : ∀ i,i.val+1<r → g i=0) (hg1 : ∀ i,i.val+1=r → IsUnit (g i)) :
    EulerCyclicShape (appendEulerBlock C g u) := by
  constructor
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>simp only [Fin.val_last] at hij;omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>simpa [appendEulerBlock] using hg0 i hij
      | cast j =>simpa [appendEulerBlock] using hC.1 i j hij
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>simp only [Fin.val_last] at hij;omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>simpa [appendEulerBlock] using hg1 i hij.symm
      | cast j =>simpa [appendEulerBlock] using hC.2 i j hij

end StrictEUnit
end
