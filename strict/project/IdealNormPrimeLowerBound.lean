import IdealNormEulerBound

noncomputable section
open scoped NumberField Topology nonZeroDivisors BigOperators
open NumberField Finset
namespace StrictEUnit

theorem idealNorm_prime_local_lower
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s)
    {p : ℕ} (hp : p.Prime) :
    1 + (idealNormCoefficient K p : ℝ) / (p : ℝ)^s ≤
      ∑' e : ℕ, idealNormRealTerm K s (p^e) := by
  have hsum := (idealNormRealTerm_summable K hs).comp_injective
    (Nat.pow_right_injective hp.one_lt)
  have h := hsum.sum_le_tsum ({0,1} : Finset ℕ)
    (fun e _ => idealNormRealTerm_nonneg K s (p^e))
  simpa only [sum_insert (by simp : (0:ℕ) ∉ ({1}:Finset ℕ)), sum_singleton,
    pow_zero, pow_one, idealNormRealTerm_one, idealNormRealTerm,
    if_neg hp.ne_zero, if_neg one_ne_zero, idealNormCoefficient_one, Nat.cast_one,
    Real.one_rpow, div_one] using h

/-- An explicit Euler lower estimate using the actual number of norm-p ideals.
No splitting-prime supply or local multiplicativity equality is assumed. -/
theorem idealNormLSeries_prime_linear_product_lower
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) (S : Finset ℕ) :
    ∏ p ∈ S with p.Prime, (1 + (idealNormCoefficient K p : ℝ) / (p : ℝ)^s) ≤
      ‖idealNormLSeries K (s : ℂ)‖ := by
  apply le_trans _ (idealNormLSeries_finite_euler_lower K hs S)
  apply Finset.prod_le_prod
  · intro p _
    positivity
  · intro p hp
    exact idealNorm_prime_local_lower K hs (mem_filter.mp hp).2

theorem idealNormCoefficient_ge_of_distinct_norm_ideals
    (K : Type*) [Field K] [NumberField K] {d p : ℕ}
    (P : Fin d → (Ideal (𝓞 K))⁰) (hP : Function.Injective P)
    (hn : ∀ i, Ideal.absNorm (P i : Ideal (𝓞 K)) = p) :
    d ≤ idealNormCoefficient K p := by
  letI := finite_idealNorm_fiber K p
  let f : Fin d → {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = p} :=
    fun i => ⟨P i, hn i⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, idealNormCoefficient] using
    Nat.card_le_card_of_injective f (fun i j h => hP (congrArg Subtype.val h))

/-- Explicit local norm-p ideal certificates may be inserted into the lower
bound; this theorem does not assert that such certificates exist for primes. -/
theorem idealNormLSeries_certified_prime_product_lower
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s)
    (S : Finset ℕ) (d : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hP : ∀ p ∈ S, ∃ P : Fin d → (Ideal (𝓞 K))⁰,
      Function.Injective P ∧ ∀ i, Ideal.absNorm (P i : Ideal (𝓞 K)) = p) :
    ∏ p ∈ S, (1 + (d : ℝ) / (p : ℝ)^s) ≤ ‖idealNormLSeries K (s : ℂ)‖ := by
  have hfilter : S.filter Nat.Prime = S := filter_true_of_mem hS
  have h := idealNormLSeries_prime_linear_product_lower K hs S
  rw [hfilter] at h
  apply le_trans _ h
  apply Finset.prod_le_prod
  · intro p _
    positivity
  · intro p hp
    obtain ⟨P, hi, hn⟩ := hP p hp
    apply add_le_add_left
    apply div_le_div_of_nonneg_right
    · exact_mod_cast idealNormCoefficient_ge_of_distinct_norm_ideals K P hi hn
    · positivity

end StrictEUnit
end
