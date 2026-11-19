import FiniteLaurentForcingArithmetic
import FiniteForcingEulerPresentation

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def zeroPaddedPowerSeriesColumn {r : ℕ} (g : Fin r →PowerSeries K) :
    (s : ℕ) →Fin (r+s) →PowerSeries K
  | 0 =>g
  | s+1 =>Fin.cases 0 (zeroPaddedPowerSeriesColumn g s)

def finiteLaurentEulerWeights {r : ℕ} (w : Fin r →ℕ) (M : ℕ) (k : ℕ →ℤ) :
    (s : ℕ) →Fin (r+s) →ℕ
  | 0 =>w
  | s+1 =>Fin.cases ((M:ℤ)+k s).toNat (finiteLaurentEulerWeights w M k s)

def finiteLaurentEulerMatrix {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ) : (s : ℕ) →Matrix (Fin (r+s)) (Fin (r+s)) (PowerSeries K)
  | 0 =>C
  | s+1 =>forcingEulerBlock (finiteLaurentEulerMatrix C g M k s)
      (zeroPaddedPowerSeriesColumn g s) (PowerSeries.C K ((M:ℤ)+k s : ℤ))

theorem finiteLaurentEuler_padded_column {r : ℕ}
    (b : Fin r →LaurentSeries K) (w : Fin r →ℕ) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ)
    (hg : ∀ i,laurentIntegerMonomial ((w i:ℤ)+1-(M:ℤ))*b i=HahnSeries.ofPowerSeries ℤ K (g i))
    (s : ℕ) : ∀ i,
      laurentIntegerMonomial ((finiteLaurentEulerWeights w M k s i:ℤ)+1-(M:ℤ))*
        zeroPaddedForcingColumn b s i=HahnSeries.ofPowerSeries ℤ K (zeroPaddedPowerSeriesColumn g s i) := by
  induction s with
  | zero =>exact hg
  | succ s ih =>
    intro i
    cases i using Fin.cases with
    | zero =>simp only [finiteLaurentEulerWeights,zeroPaddedForcingColumn,zeroPaddedPowerSeriesColumn,
        Fin.cases_zero,mul_zero,map_zero]
    | succ i =>exact ih i

/-- The same arithmetic Laurent extension has this exact regular Euler
presentation, provided the common offset makes its finitely many weights natural. -/
theorem finiteLaurentEulerMatrix_realization {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r →LaurentSeries K)
    (w : Fin r →ℕ) (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ)
    (hC : monomialEulerConnection A w=C.map (HahnSeries.ofPowerSeries ℤ K))
    (hg : ∀ i,laurentIntegerMonomial ((w i:ℤ)+1-(M:ℤ))*b i=HahnSeries.ofPowerSeries ℤ K (g i))
    (s : ℕ) (hk : ∀ j,j<s →0≤(M:ℤ)+k j) :
    monomialEulerConnection (finiteLaurentForcingConnection A b k s)
      (finiteLaurentEulerWeights w M k s)=
      (finiteLaurentEulerMatrix C g M k s).map (HahnSeries.ofPowerSeries ℤ K) := by
  induction s with
  | zero =>exact hC
  | succ s ih =>
    rw [finiteLaurentForcingConnection,finiteLaurentEulerWeights,constantForcing_monomialEulerConnection,
      ih (fun j hj =>hk j (Nat.lt_succ_of_lt hj))]
    have hn : (((M:ℤ)+k s).toNat:ℤ)=(M:ℤ)+k s := Int.toNat_of_nonneg (hk s (Nat.lt_succ_self _))
    funext i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        simp only [finiteLaurentEulerMatrix,forcingEulerBlock,Matrix.map_apply,Fin.cases_zero,
          HahnSeries.ofPowerSeries_C]
        conv_rhs => rw [← hn]
        simp only [Int.cast_natCast,map_natCast]
      | succ j =>
        simp only [finiteLaurentEulerMatrix,forcingEulerBlock,Matrix.map_apply,Fin.cases_zero,
          Fin.cases_succ,map_zero]
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp only [forcingEulerBlock,finiteLaurentEulerMatrix,Fin.cases_zero,Fin.cases_succ,Matrix.map_apply]
        change laurentIntegerMonomial _*(laurentIntegerMonomial (k s)*zeroPaddedForcingColumn b s i)=_
        rw [← mul_assoc,laurentIntegerMonomial_mul,hn]
        have he : (finiteLaurentEulerWeights w M k s i:ℤ)+1-((M:ℤ)+k s)+k s=
            (finiteLaurentEulerWeights w M k s i:ℤ)+1-(M:ℤ) := by omega
        rw [he]
        exact finiteLaurentEuler_padded_column b w g M k hg s i
      | succ j =>rfl

end StrictEUnit
end
