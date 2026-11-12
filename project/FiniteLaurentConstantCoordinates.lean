import ParallelForcingMappedAction
import GeneralizedOriginalEulerTransport

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K R : Type*} [Field K] [CharZero K] [CommRing R]

theorem constantForcingConnection_mapped_action {r : ℕ}
    (φ : LaurentSeries K →+* R) (A : Matrix (Fin r) (Fin r) (LaurentSeries K))
    (b : Fin r →LaurentSeries K) (x : Fin r →R) (a : R) :
    (Matrix.map (constantForcingConnection A b) φ).mulVec (Fin.cases a x)=
      Fin.cases 0 (fun i =>φ (b i)*a+(A.map φ).mulVec x i) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    change (∑ j : Fin (r+1),φ (constantForcingConnection A b 0 j)*Fin.cases a x j)=0
    simp [constantForcingConnection]
  | succ i =>
    change (∑ j : Fin (r+1),φ (constantForcingConnection A b i.succ j)*Fin.cases a x j)=_
    rw [Fin.sum_univ_succ]
    rfl

theorem parallelForcingVector_add_laurent_column {r : ℕ}
    (φ : LaurentSeries K →+* R) (x : Fin r →R) (h : ℕ →R)
    (b : Fin r →LaurentSeries K) (a : R) (s : ℕ) :
    (fun i =>parallelForcingVector x h s i+φ (zeroPaddedForcingColumn b s i)*a)=
      parallelForcingVector (fun i =>x i+φ (b i)*a) h s := by
  induction s with
  | zero =>rfl
  | succ s ih =>
    funext i
    cases i using Fin.cases with
    | zero =>simp [parallelForcingVector,zeroPaddedForcingColumn]
    | succ i =>exact congrFun ih i

/-- Literal constant-coordinate extension, with newest forcing coordinate first. -/
theorem finiteLaurentForcingConnection_mapped_action {r : ℕ}
    (φ : LaurentSeries K →+* R) (A : Matrix (Fin r) (Fin r) (LaurentSeries K))
    (b : Fin r →LaurentSeries K) (k : ℕ →ℤ) (x : Fin r →R) (h : ℕ →R) (s : ℕ) :
    (Matrix.map (finiteLaurentForcingConnection A b k s) φ).mulVec (parallelForcingVector x h s)=
      parallelForcingVector (fun i =>(A.map φ).mulVec x i+
        φ (b i)*∑ j ∈ Finset.range s,φ (laurentIntegerMonomial (k j))*h j) (fun _ =>0) s := by
  induction s with
  | zero =>simp [finiteLaurentForcingConnection,parallelForcingVector]
  | succ s ih =>
    rw [finiteLaurentForcingConnection,parallelForcingVector,constantForcingConnection_mapped_action,ih]
    funext i
    cases i using Fin.cases with
    | zero =>rfl
    | succ i =>
      simp only [Fin.cases_succ,map_mul]
      have he := congrFun (parallelForcingVector_add_laurent_column φ
        (fun i =>(A.map φ).mulVec x i+φ (b i)*∑ j ∈ Finset.range s,φ (laurentIntegerMonomial (k j))*h j)
        (fun _ =>0) b (φ (laurentIntegerMonomial (k s))*h s) s) i
      have hr : φ (HahnSeries.single (k s) (1:K))*φ (zeroPaddedForcingColumn b s i)*h s=
          φ (zeroPaddedForcingColumn b s i)*(φ (laurentIntegerMonomial (k s))*h s) := by
        change φ (laurentIntegerMonomial (k s))*φ (zeroPaddedForcingColumn b s i)*h s=_
        ring
      rw [hr,add_comm,he]
      simp only [parallelForcingVector,Fin.cases_succ,Finset.sum_range_succ]
      congr 2
      funext j
      ring

theorem finiteLaurentForcingConnection_mapped_equation_iff {r : ℕ}
    (φ : LaurentSeries K →+* R) (D : R →R)
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r →LaurentSeries K)
    (k : ℕ →ℤ) (x : Fin r →R) (h : ℕ →R) (s : ℕ) :
    (∀ i,D (parallelForcingVector x h s i)=
      (Matrix.map (finiteLaurentForcingConnection A b k s) φ).mulVec (parallelForcingVector x h s) i) ↔
      (∀ i,D (x i)=(A.map φ).mulVec x i+
        φ (b i)*∑ j ∈ Finset.range s,φ (laurentIntegerMonomial (k j))*h j) ∧
      (∀ j,j<s →D (h j)=0) := by
  rw [← funext_iff,parallelForcingVector_map,finiteLaurentForcingConnection_mapped_action,
    parallelForcingVector_eq_iff,funext_iff]

end StrictEUnit
end
