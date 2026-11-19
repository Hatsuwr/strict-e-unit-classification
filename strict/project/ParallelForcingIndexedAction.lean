import FiniteLaurentEulerPresentation
import ParallelForcingCompanion

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Same recursive ordering as the actual finite Laurent forcing extension.
The newest forcing mode is first; the source coordinates remain last. -/
def parallelForcingVector {R : Type*} {r : ℕ} (x : Fin r → R) (h : ℕ → R) :
    (s : ℕ) → Fin (r+s) → R
  | 0 => x
  | s+1 => Fin.cases (h s) (parallelForcingVector x h s)

theorem forcingEulerBlock_mulVec {R : Type*} [CommRing R] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) R) (g x : Fin r → R) (u a : R) :
    (forcingEulerBlock C g u).mulVec (Fin.cases a x)=
      Fin.cases (u*a) (fun i =>g i*a+C.mulVec x i) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    change (∑ j : Fin (r+1), forcingEulerBlock C g u 0 j * Fin.cases a x j)=_
    rw [Fin.sum_univ_succ]
    simp [forcingEulerBlock]
  | succ i =>
    change (∑ j : Fin (r+1), forcingEulerBlock C g u i.succ j * Fin.cases a x j)=_
    rw [Fin.sum_univ_succ]
    rfl

theorem parallelForcingVector_map {R S : Type*} {r : ℕ}
    (f : R → S) (x : Fin r → R) (h : ℕ → R) (s : ℕ) :
    (fun i => f (parallelForcingVector x h s i)) =
      parallelForcingVector (fun i =>f (x i)) (fun j =>f (h j)) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact congrFun ih i

theorem parallelForcingVector_eq_iff {R : Type*} {r : ℕ}
    (x y : Fin r → R) (h l : ℕ → R) (s : ℕ) :
    parallelForcingVector x h s=parallelForcingVector y l s ↔
      x=y ∧ ∀ j,j<s → h j=l j := by
  induction s with
  | zero => simp [parallelForcingVector]
  | succ s ih =>
    constructor
    · intro he
      have hs : parallelForcingVector x h s=parallelForcingVector y l s :=
        funext (fun i =>congrFun he i.succ)
      obtain ⟨hxy,ht⟩ := ih.mp hs
      refine ⟨hxy,fun j hj =>?_⟩
      by_cases hj' : j<s
      · exact ht j hj'
      · have hj : j=s := by omega
        subst j
        exact congrFun he 0
    · rintro ⟨hxy,ht⟩
      have hs := ih.mpr ⟨hxy,fun j hj =>ht j (by omega)⟩
      funext i
      cases i using Fin.cases with
      | zero => exact ht s (by omega)
      | succ i => exact congrFun hs i

variable {K : Type*} [Field K] [CharZero K]

/-- Adding a source column changes only the source coordinates. -/
theorem parallelForcingVector_add_column {r : ℕ}
    (x : Fin r → PowerSeries K) (h : ℕ → PowerSeries K)
    (g : Fin r → PowerSeries K) (a : PowerSeries K) (s : ℕ) :
    (fun i => parallelForcingVector x h s i + zeroPaddedPowerSeriesColumn g s i * a) =
      parallelForcingVector (fun i => x i+g i*a) h s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    funext i
    cases i using Fin.cases with
    | zero => simp [parallelForcingVector,zeroPaddedPowerSeriesColumn]
    | succ i => exact congrFun ih i

/-- Exact action of the actual recursively indexed matrix. No index
permutation or moment identification is left implicit. -/
theorem finiteLaurentEulerMatrix_mul_parallel {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r → PowerSeries K)
    (M : ℕ) (k : ℕ → ℤ) (x : Fin r → PowerSeries K) (h : ℕ → PowerSeries K)
    (s : ℕ) :
    (finiteLaurentEulerMatrix C g M k s).mulVec (parallelForcingVector x h s) =
      parallelForcingVector
        (fun i => C.mulVec x i + g i * ∑ j ∈ Finset.range s, h j)
        (fun j => PowerSeries.C K (((M:ℤ)+k j):K) * h j) s := by
  induction s with
  | zero => simp [finiteLaurentEulerMatrix,parallelForcingVector]
  | succ s ih =>
    rw [finiteLaurentEulerMatrix,parallelForcingVector,forcingEulerBlock_mulVec,ih]
    funext i
    cases i using Fin.cases with
    | zero => simp [parallelForcingVector,Int.cast_add]
    | succ i =>
      simp only [Fin.cases_succ]
      have he := congrFun (parallelForcingVector_add_column
        (fun i => C.mulVec x i+g i*∑ j ∈ Finset.range s,h j)
        (fun j => PowerSeries.C K (((M:ℤ)+k j):K)*h j) g (h s) s) i
      rw [add_comm,he]
      simp only [parallelForcingVector,Fin.cases_succ,Finset.sum_range_succ]
      congr 2
      funext j
      ring

/-- Full indexed differential equation, with its exact forcing sum. This
identity applies to any coefficientwise operator; no derivative law is assumed. -/
theorem finiteLaurentEulerMatrix_equation_iff {r : ℕ}
    (D : PowerSeries K → PowerSeries K)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r → PowerSeries K)
    (M : ℕ) (k : ℕ → ℤ) (x : Fin r → PowerSeries K) (h : ℕ → PowerSeries K)
    (s : ℕ) :
    (∀ i,D (parallelForcingVector x h s i)=
      (finiteLaurentEulerMatrix C g M k s).mulVec (parallelForcingVector x h s) i) ↔
      (∀ i,D (x i)=C.mulVec x i+g i*∑ j ∈ Finset.range s,h j) ∧
      (∀ j,j<s →D (h j)=PowerSeries.C K (((M:ℤ)+k j):K)*h j) := by
  rw [← funext_iff,parallelForcingVector_map,finiteLaurentEulerMatrix_mul_parallel,
    parallelForcingVector_eq_iff,funext_iff]


end StrictEUnit
end
