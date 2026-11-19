import SignedLaplaceExplicitBoundary

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The literal signed ordinary input, without substituting a nonzero center. -/
def signedOrdinarySource (a : ℕ → K) : LaurentSeries K :=
  HahnSeries.single (1:ℤ) (1:K) *
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => (-1:K)^n * a n)

theorem signedOrdinarySource_coeff_lt_one (a : ℕ → K) (m : ℤ) (hm : m < 1) :
    (signedOrdinarySource a).coeff m = 0 := by
  rw [signedOrdinarySource, signedLaplace_single_coeff, one_mul]
  exact powerSeries_laurent_coeff_neg _ _ (by omega)

theorem signedLaplace_Dz_lower_support (y : LaurentSeries K) (L : ℤ)
    (hL : ∀ m : ℤ, m < L → y.coeff m = 0) (i : ℕ) :
    ∀ m : ℤ, m < L+(i:ℤ) →
      ((fun x : LaurentSeries K => HahnSeries.single (2:ℤ) (-1:K) *
        laurentOrdinaryDerivation x)^[i] y).coeff m = 0 := by
  induction i with
  | zero => simpa only [Nat.cast_zero, add_zero, Function.iterate_zero_apply] using hL
  | succ i ih =>
    intro m hm
    rw [Function.iterate_succ_apply', signedLaplace_single_coeff,
      laurentOrdinaryDerivation_coeff]
    have hz := ih (m-2+1) (by omega)
    rw [hz, mul_zero, mul_zero]

theorem signedLaplace_z_lower_support (y : LaurentSeries K) (L : ℤ)
    (hL : ∀ m : ℤ, m < L → y.coeff m = 0) (j : ℕ) :
    ∀ m : ℤ, m < L-(j:ℤ) →
      ((fun x : LaurentSeries K => HahnSeries.single (-1:ℤ) (1:K) * x)^[j] y).coeff m = 0 := by
  induction j with
  | zero => simpa only [Nat.cast_zero, sub_zero, Function.iterate_zero_apply] using hL
  | succ j ih =>
    intro m hm
    rw [Function.iterate_succ_apply', signedLaplace_single_coeff, one_mul]
    exact ih (m-(-1)) (by omega)

/-- The finite array itself derives the lower support 1-nu for canonical
input; no support or error-polynomial premise is supplied. -/
theorem signedLaplaceSourceAction_canonical_lower_support {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) :
    ∀ m : ℤ, m < 1-(ν:ℤ) →
      (signedLaplaceSourceAction A (signedOrdinarySource a)).coeff m = 0 := by
  classical
  intro m hm
  unfold signedLaplaceSourceAction
  simp only [HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [signedLaplace_single_coeff, sub_zero]
  have hD := signedLaplace_Dz_lower_support (signedOrdinarySource a) 1
    (signedOrdinarySource_coeff_lt_one a) i.val
  have hz := signedLaplace_z_lower_support _ (1+(i.val:ℤ)) hD j.val
  have hjν : j.val ≤ ν := Nat.le_of_lt_succ j.isLt
  rw [hz m (by omega), mul_zero]

/-- Reverse the nonpositive Laurent coefficients and truncate at exactly nu. -/
def laurentFirstNuBoundary (ν : ℕ) (S : LaurentSeries K) : Polynomial K :=
  PowerSeries.trunc ν (PowerSeries.mk fun k => S.coeff (-(k:ℤ)))

theorem laurentFirstNuBoundary_coeff (ν : ℕ) (S : LaurentSeries K) (k : ℕ) :
    (laurentFirstNuBoundary ν S).coeff k = if k < ν then S.coeff (-(k:ℤ)) else 0 := by
  simp only [laurentFirstNuBoundary, PowerSeries.coeff_trunc, PowerSeries.coeff_mk]

theorem laurentFirstNuBoundary_natDegree_le (ν : ℕ) (hν : 0 < ν) (S : LaurentSeries K) :
    (laurentFirstNuBoundary ν S).natDegree ≤ ν-1 := by
  have h := PowerSeries.natDegree_trunc_lt
    (PowerSeries.mk fun k => S.coeff (-(k:ℤ))) (ν-1)
  have he : ν-1+1=ν := by omega
  simpa only [laurentFirstNuBoundary, he] using Nat.lt_succ_iff.mp h

theorem signedInverseLaplace_firstNu_reconstruct
    (ν : ℕ) (S : LaurentSeries K)
    (hlow : ∀ m : ℤ, m < 1-(ν:ℤ) → S.coeff m = 0)
    (hzero : signedInverseLaplace S = 0) :
    S = signedLaplacePolynomialInZ (laurentFirstNuBoundary ν S) := by
  have hpos := (signedInverseLaplace_eq_zero_iff S).1 hzero
  ext m
  rw [signedLaplacePolynomialInZ_coeff]
  by_cases hm : m ≤ 0
  · rw [if_pos hm, laurentFirstNuBoundary_coeff]
    have hk : (((-m).toNat : ℕ):ℤ) = -m := Int.toNat_of_nonneg (by omega)
    by_cases hkm : (-m).toNat < ν
    · rw [if_pos hkm, hk, neg_neg]
    · rw [if_neg hkm]
      exact hlow m (by omega)
  · rw [if_neg hm]
    have hmi : 0 ≤ m-1 := by omega
    have he : (((m-1).toNat : ℕ):ℤ)+1=m := by
      rw [Int.toNat_of_nonneg hmi]
      omega
    rw [← he]
    exact hpos (m-1).toNat

/-- Explicit nu-cutoff boundary for the SAME canonical source action. -/
def signedLaplaceFirstNuBoundary {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) : Polynomial K :=
  laurentFirstNuBoundary ν (signedLaplaceSourceAction A (signedOrdinarySource a))

theorem signedLaplace_firstNu_fourier_iff {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) :
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val]
        (PowerSeries.mk fun n => a n/(n.factorial:K))) = 0) ↔
      signedLaplaceSourceAction A (signedOrdinarySource a) =
        signedLaplacePolynomialInZ (signedLaplaceFirstNuBoundary A a) := by
  have he := signedLaplace_sourceAction A (signedOrdinarySource a)
  rw [signedOrdinarySource, signedInverseLaplace_signed_input] at he
  rw [← he]
  constructor
  · intro hz
    exact signedInverseLaplace_firstNu_reconstruct ν _
      (signedLaplaceSourceAction_canonical_lower_support A a) hz
  · intro hs
    change signedInverseLaplace (signedLaplaceSourceAction A (signedOrdinarySource a)) = 0
    rw [hs, signedInverseLaplace_polynomialInZ]

theorem signedLaplaceFirstNuBoundary_natDegree_le {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hν : 0 < ν) (a : ℕ → K) :
    (signedLaplaceFirstNuBoundary A a).natDegree ≤ ν-1 :=
  laurentFirstNuBoundary_natDegree_le ν hν _

end StrictEUnit
end
