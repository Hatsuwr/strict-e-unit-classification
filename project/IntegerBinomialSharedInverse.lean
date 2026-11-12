import NaturalBinomialSharedInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Integer inputs have integral binomial values, including negative inputs. -/
theorem resonance_integer_choose_integral (z : ℤ) (m : ℕ) :
    IsIntegral ℤ (Ring.choose (z : K) m) := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast,Int.cast_natCast,Ring.choose_natCast]
    exact ordinaryJet_natCast_integral _
  | negSucc n =>
    have h := binomial_negative_cleared_prefix (K:=K) ((n+1 : ℕ) : K) 1 m
      (by intro j hj
          simp only [Nat.cast_one,one_mul,Ring.choose_natCast]
          exact ordinaryJet_natCast_integral _) m le_rfl
    simpa only [Nat.cast_one,one_mul,Int.cast_negSucc,Nat.cast_add,Nat.cast_one] using h

theorem resonance_negative_choose (n m : ℕ) :
    Ring.choose (-((n+1 : ℕ) : K)) m = (-1 : K)^m*((n+m).choose m : K) := by
  rw [Ring.choose_neg]
  have he : ((n+1 : ℕ) : K)+(m : K)-1=((n+m : ℕ) : K) := by push_cast;ring
  rw [he,Ring.choose_natCast]
  rw [Units.smul_def,zsmul_eq_mul,Int.cast_negOnePow_natCast]

/-- One LCM clears every nonzero integer-binomial inverse in the stated
range. Negative top indices are included; zero pivots are NOT inverted. -/
theorem resonance_integer_choose_inverse_lcm (N : ℕ) (z : ℤ) (m : ℕ)
    (hsize : z.natAbs+m≤N) (hne : Ring.choose (z : K) m≠0) :
    IsIntegral ℤ ((logJetLCM N : K)*(Ring.choose (z : K) m)⁻¹) := by
  cases z with
  | ofNat n =>
    change n+m≤N at hsize
    rw [Int.ofNat_eq_natCast,Int.cast_natCast,Ring.choose_natCast] at hne ⊢
    have hm : m≤n := by
      by_contra h
      have hz : n.choose m=0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hz,Nat.cast_zero,ne_eq,not_true_eq_false] at hne
    simpa only [div_eq_mul_inv] using integral_nat_quotient_of_dvd (K:=K) _ _ (Nat.choose_pos hm)
      (nat_choose_dvd_logJetLCM N n m (by omega) hm)
  | negSucc n =>
    simp only [Int.natAbs_negSucc] at hsize
    rw [Int.cast_negSucc,resonance_negative_choose,mul_inv_rev,← inv_pow,inv_neg,inv_one]
    have h := integral_nat_quotient_of_dvd (K:=K) (logJetLCM N) ((n+m).choose m)
      (Nat.choose_pos (by omega)) (nat_choose_dvd_logJetLCM N (n+m) m (by omega) (by omega))
    convert h.mul ((ordinaryJet_natCast_integral (K:=K) 1).neg.pow m) using 1 <;>
      simp only [Nat.cast_one,div_eq_mul_inv] <;> ring

/-- The same LCM power clears a whole fixed-length product, uniformly in all
integer top indices and nonzero pivots in the prefix. -/
theorem resonance_integer_products_inverse_lcm (N q : ℕ) (z : Fin q → ℤ)
    (ms : Fin q → ℕ) (hsize : ∀ i,(z i).natAbs+ms i≤N)
    (hne : (∏ i : Fin q,Ring.choose (z i : K) (ms i))≠0) :
    IsIntegral ℤ (((logJetLCM N^q : ℕ) : K)*
      (∏ i : Fin q,Ring.choose (z i : K) (ms i))⁻¹) := by
  have hi (i : Fin q) := resonance_integer_choose_inverse_lcm (K:=K) N (z i) (ms i)
    (hsize i) ((Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ _))
  convert IsIntegral.prod (s:=Finset.univ) _ (fun i _ => hi i) using 1
  simp only [Nat.cast_pow,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Finset.prod_inv_distrib]

end StrictEUnit
end
