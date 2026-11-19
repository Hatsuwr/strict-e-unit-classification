import MonomialEulerPresentation

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

/-- Regular Euler block extension, with a scalar residue in the new first row. -/
def forcingEulerBlock {R : Type*} [Zero R] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) R) (g : Fin r → R) (u : R) :
    Matrix (Fin (r+1)) (Fin (r+1)) R :=
  Fin.cases (Fin.cases u (fun _ =>0)) (fun i =>Fin.cases (g i) (fun j =>C i j))

variable {K : Type*} [Field K]

/-- Exact four-block computation of the same constant-forcing gauge. -/
theorem constantForcing_monomialEulerConnection {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (w : Fin r → ℕ) (u : ℕ) :
    monomialEulerConnection (constantForcingConnection A b) (Fin.cases u w)=
      forcingEulerBlock (monomialEulerConnection A w)
        (fun i =>laurentIntegerMonomial ((w i : ℤ)+1-(u : ℤ))*b i) (u : LaurentSeries K) := by
  funext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [monomialEulerConnection,constantForcingConnection,forcingEulerBlock,Matrix.one_apply,Fin.ext_iff]

/-- The actual natural gauge weights, highest forcing derivative first. -/
def polynomialForcingEulerWeights {r : ℕ} (w : Fin r → ℕ) (u : ℕ) :
    (d : ℕ) →Fin ((r+1)+d) →ℕ
  | 0 =>Fin.cases u w
  | d+1 =>Fin.cases (u+d+1) (polynomialForcingEulerWeights w u d)

/-- The regular Euler matrix for the same finite forcing chain. -/
def polynomialForcingEulerMatrix {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r → PowerSeries K) (u : ℕ) :
    (d : ℕ) →Matrix (Fin ((r+1)+d)) (Fin ((r+1)+d)) (PowerSeries K)
  | 0 =>forcingEulerBlock C g (PowerSeries.C K (u : K))
  | d+1 =>forcingEulerBlock (polynomialForcingEulerMatrix C g u d)
      (fun i =>if i.val=0 then 1 else 0) (PowerSeries.C K ((u+d+1 : ℕ) : K))

theorem polynomialForcingEulerWeights_zero {r : ℕ} (w : Fin r → ℕ) (u d : ℕ) :
    polynomialForcingEulerWeights w u d 0=u+d := by
  cases d <;> simp [polynomialForcingEulerWeights,Nat.add_assoc]

/-- Once the first forcing column is regular, EVERY finite forcing chain has
an exact regular Euler realization under the displayed natural weights. -/
theorem polynomialForcingEulerMatrix_realization {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (w : Fin r → ℕ) (u : ℕ)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r → PowerSeries K)
    (hC : monomialEulerConnection A w=C.map (HahnSeries.ofPowerSeries ℤ K))
    (hg : ∀ i,laurentIntegerMonomial ((w i : ℤ)+1-(u : ℤ))*b i=HahnSeries.ofPowerSeries ℤ K (g i)) :
    ∀ d,monomialEulerConnection (polynomialForcingConnection A b d)
      (polynomialForcingEulerWeights w u d)=
        (polynomialForcingEulerMatrix C g u d).map (HahnSeries.ofPowerSeries ℤ K) := by
  intro d
  induction d with
  | zero =>
    rw [polynomialForcingConnection,polynomialForcingEulerWeights,constantForcing_monomialEulerConnection,hC]
    funext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [polynomialForcingEulerMatrix,forcingEulerBlock,Matrix.map_apply,hg,
        HahnSeries.ofPowerSeries_C]
  | succ d ih =>
    letI : NeZero ((r+1)+d) := ⟨by omega⟩
    rw [polynomialForcingConnection,polynomialForcingEulerWeights,constantForcing_monomialEulerConnection,ih]
    funext i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases <;>
        simp [polynomialForcingEulerMatrix,forcingEulerBlock,Matrix.map_apply,HahnSeries.ofPowerSeries_C]
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp only [forcingEulerBlock,Fin.cases_succ,Fin.cases_zero,polynomialForcingEulerMatrix,Matrix.map_apply]
        by_cases hi : i.val=0
        · have hi0 : i=0 := Fin.ext hi
          subst i
          rw [polynomialForcingEulerWeights_zero]
          simp [laurentIntegerMonomial_zero]
        · simp [hi]
      | succ j =>rfl

end StrictEUnit
end
