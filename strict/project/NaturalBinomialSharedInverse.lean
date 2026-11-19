import LogJetLCMExponential

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Prime-valuation bound obtained directly from mathlib's Kummer formula.
This is the positive-binomial case of mathlib's factorization_choose_le_log;
its proof is reproduced here to use the already cached multiplicity modules. -/
theorem nat_choose_prime_factorization_le_log (n k p : ℕ) (hp : p.Prime) (hk : k≤n) :
    (n.choose k).factorization p≤Nat.log p n := by
  rw [Nat.factorization_def _ hp,@padicValNat_def _ ⟨hp⟩ _ (Nat.choose_pos hk)]
  rw [← Nat.cast_le (α:=ℕ∞),← FiniteMultiplicity.emultiplicity_eq_multiplicity]
  · simp only [hp.emultiplicity_choose hk (Nat.lt_succ_self _),Nat.cast_le]
    exact (Finset.card_filter_le _ _).trans (le_of_eq (Nat.card_Ico _ _))
  · exact Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one,Nat.choose_pos hk⟩

/-- All positive binomial integers with top index at most N divide the SAME
LCM, rather than needing a product of individual inverse certificates. -/
theorem nat_choose_dvd_logJetLCM (N n k : ℕ) (hn : n≤N) (hk : k≤n) :
    n.choose k∣logJetLCM N := by
  by_cases hn0 : n=0
  · subst n
    have hk0 : k=0 := by omega
    subst k
    simp
  apply (Nat.factorization_prime_le_iff_dvd (ne_of_gt (Nat.choose_pos hk))
    (ne_of_gt (logJetLCM_pos N))).1
  intro p hp
  apply (hp.pow_dvd_iff_le_factorization (ne_of_gt (logJetLCM_pos N))).1
  apply logJetLCM_dvd N _ (pow_pos hp.pos _)
  exact (Nat.pow_le_of_le_log hn0 (nat_choose_prime_factorization_le_log n k p hp hk)).trans hn

/-- A genuinely SHARED inverse denominator for natural-binomial products.
This is a restricted arithmetic case, not a rationality claim for the actual
Fourier exponent differences. -/
theorem natural_binomial_products_shared_inverse_denominators
    {K : Type*} [Field K] [CharZero K] (q : ℕ) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ (a b : Fin q → ℕ),(∀ i,a i≤N) → (∀ i,b i≤a i) →
        IsIntegral ℤ ((D : K)*(∏ i : Fin q,Ring.choose (a i : K) (b i))⁻¹) := by
  refine ⟨(16 : ℝ)^q,one_le_pow₀ (by norm_num),?_⟩
  intro N
  refine ⟨logJetLCM N^q,pow_pos (logJetLCM_pos N) _,?_,?_⟩
  · rw [Nat.cast_pow]
    calc
      (logJetLCM N : ℝ)^q≤((16 : ℝ)^N)^q :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (logJetLCM_real_le_sixteen_pow N) q
      _ =((16 : ℝ)^q)^N := by rw [← pow_mul,← pow_mul];congr 1;ring
      _ ≤((16 : ℝ)^q)^(N+1) := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (Nat.le_succ _)
  · intro a b ha hb
    have hi (i : Fin q) : IsIntegral ℤ ((logJetLCM N : K)/((a i).choose (b i) : K)) :=
      integral_nat_quotient_of_dvd _ _ (Nat.choose_pos (hb i))
        (nat_choose_dvd_logJetLCM N (a i) (b i) (ha i) (hb i))
    convert IsIntegral.prod (s:=Finset.univ) _ (fun i _ => hi i) using 1
    simp only [Ring.choose_natCast,Nat.cast_pow,Finset.prod_div_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin,div_eq_mul_inv,
      Finset.prod_mul_distrib,Finset.prod_inv_distrib]

end StrictEUnit
end
