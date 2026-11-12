import ConstantForcingDividedFormula

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- One common explicit prefix integer clears the forcing column. The
increased old cutoff is linear in N; the only new denominator is LCM(N)^2. -/
theorem constantForcingColumn_prefix_integral {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (P W N DA DB : ℕ)
    (hAlow : ∀ a,a≤N →∀ i j l,l< -((P*a : ℕ) : ℤ) →
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K)).coeff l=0)
    (hblow : ∀ j l,l< -(W : ℤ) →(b j).coeff l=0)
    (hA : ∀ a,a≤N →∀ i j l,l≤(((P+W+3)*(N+1) : ℕ) : ℤ) →
      IsIntegral ℤ ((DA : K)*(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K)).coeff l))
    (hb : ∀ j l,l≤(((P+W+3)*(N+1) : ℕ) : ℤ) →IsIntegral ℤ ((DB : K)*(b j).coeff l)) :
    ∀ m,m≤N →∀ i l,l≤(N : ℤ) →IsIntegral ℤ (((DA*DB*logJetLCM N^2 : ℕ) : K)*
      (constantForcingColumn (stage14_laurentAlgebraDerivation (k:=K)) A b m i/
        (m.factorial : LaurentSeries K)).coeff l) := by
  intro m hm i l hl
  rw [constantForcingColumn_divided_coeff,Finset.mul_sum]
  apply IsIntegral.sum
  intro a ha
  have ham : a<m := Finset.mem_range.mp ha
  have haN : a≤N := by omega
  have hprod : ∀ k,k≤((2*N : ℕ) : ℤ) →IsIntegral ℤ (((DA*DB : ℕ) : K)*
      (∑ j,(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K))*b j).coeff k) := by
    intro k hk
    rw [HahnSeries.coeff_sum,Finset.mul_sum]
    apply IsIntegral.sum
    intro j hj
    have hleft : ((2*N : ℕ) : ℤ)-(-(W : ℤ))≤(((P+W+3)*(N+1) : ℕ) : ℤ) := by
      push_cast
      have hP : (0 : ℤ)≤P := Int.natCast_nonneg _
      have hW : (0 : ℤ)≤W := Int.natCast_nonneg _
      have hN : (0 : ℤ)≤N := Int.natCast_nonneg _
      nlinarith
    have hright : ((2*N : ℕ) : ℤ)-(-((P*a : ℕ) : ℤ))≤(((P+W+3)*(N+1) : ℕ) : ℤ) := by
      have hpa : P*a≤P*N := Nat.mul_le_mul_left P haN
      have hpa' : ((P*a : ℕ) : ℤ)≤((P*N : ℕ) : ℤ) := by exact_mod_cast hpa
      push_cast at hpa' ⊢
      have hP : (0 : ℤ)≤P := Int.natCast_nonneg _
      have hW : (0 : ℤ)≤W := Int.natCast_nonneg _
      have hN : (0 : ℤ)≤N := Int.natCast_nonneg _
      nlinarith
    simpa only [Nat.cast_mul] using forcing_laurent_product_integral _ (b j)
      (-((P*a : ℕ) : ℤ)) (-(W : ℤ)) ((2*N : ℕ) : ℤ) (DA : K) (DB : K)
      (hAlow a haN i j) (hblow j)
      (fun v hv =>hA a haN i j v (hv.trans hleft))
      (fun v hv =>hb j v (hv.trans hright)) k hk
  have hH := forcing_laurent_hasse_integral
    (∑ j,(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
      (a.factorial : LaurentSeries K))*b j) (m-1-a) l ((DA*DB : ℕ) : K)
      (hprod _ (by have hh : ((m-1-a : ℕ) : ℤ)≤(N : ℤ) := by exact_mod_cast (show m-1-a≤N by omega)
                   push_cast
                   omega))
  have hR := forcing_factorial_ratio_lcm_integral (K:=K) N m a hm ham
  convert hR.mul hH using 1 <;> push_cast <;> ring

/-- All four matrix blocks share the same clearing integer. -/
theorem constantForcingConnection_prefix_integral {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (P W N DA DB : ℕ)
    (hAlow : ∀ a,a≤N →∀ i j l,l< -((P*a : ℕ) : ℤ) →
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K)).coeff l=0)
    (hblow : ∀ j l,l< -(W : ℤ) →(b j).coeff l=0)
    (hA : ∀ a,a≤N →∀ i j l,l≤(((P+W+3)*(N+1) : ℕ) : ℤ) →
      IsIntegral ℤ ((DA : K)*(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K)).coeff l))
    (hb : ∀ j l,l≤(((P+W+3)*(N+1) : ℕ) : ℤ) →IsIntegral ℤ ((DB : K)*(b j).coeff l)) :
    ∀ m,m≤N →∀ i j l,l≤(N : ℤ) →IsIntegral ℤ (((DA*DB*logJetLCM N^2 : ℕ) : K)*
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K))
        (constantForcingConnection A b) m i j/(m.factorial : LaurentSeries K)).coeff l) := by
  intro m hm i j l hl
  obtain ⟨htop,hmain,hcol⟩ := constantForcingConnection_sequence
    (stage14_laurentAlgebraDerivation (k:=K)) A b m
  cases i using Fin.cases with
  | zero =>
    rw [htop]
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      simp only [Nat.factorial_zero,Nat.cast_one,div_one,HahnSeries.coeff_one]
      split_ifs <;> simp only [mul_one,mul_zero]
      · exact ordinaryJet_natCast_integral _
      · exact isIntegral_zero
    · simp only [zero_div,HahnSeries.coeff_zero,mul_zero]
      exact isIntegral_zero
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [hcol]
      exact constantForcingColumn_prefix_integral A b P W N DA DB hAlow hblow hA hb m hm i l hl
    | succ j =>
      rw [hmain]
      have hh := hA m hm i j l (hl.trans (by push_cast; nlinarith [Int.natCast_nonneg P,Int.natCast_nonneg W,Int.natCast_nonneg N]))
      convert hh.mul (ordinaryJet_natCast_integral (K:=K) (DB*logJetLCM N^2)) using 1 <;> push_cast <;> ring

end StrictEUnit
end
