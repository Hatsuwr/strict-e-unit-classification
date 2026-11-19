import LogSolutionConnectionIntertwining
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Actual coefficients of repeated Euler differentiation of coordinate zero. -/
def eulerCyclicRow {n : ℕ} (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K)) :
    ℕ → Fin (n+1) → PowerSeries K
  | 0 => fun j => if j=0 then 1 else 0
  | m+1 => powerSeriesEulerRowConnection C (eulerCyclicRow C m)

def eulerCyclicJetMatrix {n : ℕ} (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K)) :
    Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K) := fun i =>eulerCyclicRow C i.val

/-- Upper-Hessenberg support forces the actual jet change to be lower triangular. -/
theorem eulerCyclicRow_support {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hC : ∀ i j,i.val+1<j.val → C i j=0) (m : ℕ) (j : Fin (n+1))
    (hj : m<j.val) : eulerCyclicRow C m j=0 := by
  induction m generalizing j with
  | zero =>
    have h : j≠0 := by intro h;subst j;simp at hj
    simp [eulerCyclicRow,h]
  | succ m ih =>
    change powerSeriesEuler (eulerCyclicRow C m j)+(∑ l,eulerCyclicRow C m l*C l j)=0
    rw [ih j (by omega)]
    have hs : (∑ l,eulerCyclicRow C m l*C l j)=0 := by
      apply Finset.sum_eq_zero
      intro l hl
      by_cases h : m<l.val
      · rw [ih l h,zero_mul]
      · rw [hC l j (by omega),mul_zero]
    simp [powerSeriesEuler,hs]

/-- The diagonal is the successive product of the actual superdiagonal pivots. -/
theorem eulerCyclicRow_diagonal_step {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hC : ∀ i j,i.val+1<j.val → C i j=0) (i : Fin n) :
    eulerCyclicRow C (i.val+1) i.succ=
      eulerCyclicRow C i.val i.castSucc*C i.castSucc i.succ := by
  change powerSeriesEuler (eulerCyclicRow C i.val i.succ)+
    (∑ l,eulerCyclicRow C i.val l*C l i.succ)=_
  rw [eulerCyclicRow_support C hC i.val i.succ (by simp)]
  simp only [powerSeriesEuler,map_zero,mul_zero,zero_add]
  apply Finset.sum_eq_single i.castSucc
  · intro l hl hne
    by_cases h : i.val<l.val
    · rw [eulerCyclicRow_support C hC i.val l h,zero_mul]
    · have hlt : l.val < i.val := by
        have hn : l.val≠i.val := by intro he;apply hne;exact Fin.ext he
        omega
      rw [hC l i.succ (by simp only [Fin.val_succ];omega),mul_zero]
  · simp

theorem eulerCyclicJetMatrix_diagonal_isUnit {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hC : ∀ i j,i.val+1<j.val → C i j=0)
    (hp : ∀ i : Fin n,IsUnit (C i.castSucc i.succ)) (i : Fin (n+1)) :
    IsUnit (eulerCyclicJetMatrix C i i) := by
  have h : ∀ m (hm : m<n+1),IsUnit (eulerCyclicRow C m ⟨m,hm⟩) := by
    intro m
    induction m with
    | zero =>intro hm;simp [eulerCyclicRow]
    | succ m ih =>
      intro hm
      let j : Fin n := ⟨m,by omega⟩
      change IsUnit (eulerCyclicRow C (j.val+1) j.succ)
      rw [eulerCyclicRow_diagonal_step C hC j]
      exact (ih (by omega)).mul (hp j)
  exact h i.val i.isLt

/-- A genuine unit determinant, derived from matrix support and its pivots. -/
theorem eulerCyclicJetMatrix_det_isUnit {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hC : ∀ i j,i.val+1<j.val → C i j=0)
    (hp : ∀ i : Fin n,IsUnit (C i.castSucc i.succ)) :
    IsUnit (eulerCyclicJetMatrix C).det := by
  rw [Matrix.det_of_lowerTriangular (eulerCyclicJetMatrix C) (by
    intro i j hij
    exact eulerCyclicRow_support C hC i.val j hij)]
  apply Finset.prod_induction
  · intro a b ha hb;exact ha.mul hb
  · exact isUnit_one
  · intro i hi;exact eulerCyclicJetMatrix_diagonal_isUnit C hC hp i

/-- The constructed coefficients really are the twisted Euler jets of EVERY
logarithmic solution, with its exponent retained exactly. -/
theorem eulerCyclicRow_log_solution {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K)) (rho : K)
    (Y : Fin (n+1) →Polynomial (LaurentSeries K))
    (hY : ∀ i,twistedLogPolynomialEuler rho (Y i)=∑ j,logPowerSeriesEmbedding (C i j)*Y j)
    (m : ℕ) :
    (twistedLogPolynomialEuler rho)^[m] (Y 0)=
      ∑ j,logPowerSeriesEmbedding (eulerCyclicRow C m j)*Y j := by
  induction m with
  | zero =>simp [eulerCyclicRow]
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih]
    exact logSolutionRowPairing_intertwines C rho Y hY (eulerCyclicRow C m)

end StrictEUnit
end
