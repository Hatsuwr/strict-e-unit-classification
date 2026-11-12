import NegativeOnePrimeCertificates
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.GoingUp

noncomputable section
open scoped NumberField
namespace StrictEUnit

/-- Every rational prime has an actual discrete place in a number field,
with the same value-group type for every prime. -/
theorem numberField_exists_prime_place (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    ∃ v : Valuation K (WithZero (Multiplicative ℤ)), v (p : K) < 1 := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpn : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  letI : P.IsPrime := (Ideal.span_singleton_prime hpn).mpr (Nat.prime_iff_prime_int.mp hp)
  have hker : (⊥ : Ideal (𝓞 K)).comap (algebraMap ℤ (𝓞 K)) ≤ P := by
    change RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ P
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
    exact bot_le
  obtain ⟨Q, _, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 K)) hker
  have hmem : (p : 𝓞 K) ∈ Q := by
    have h : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQP]; exact Ideal.subset_span (by simp)
    simpa using h
  have hne : Q ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hmem
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) hmem
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, hne⟩
  refine ⟨w.valuation K, ?_⟩
  have hlt := (w.valuation_lt_one_iff_dvd (K := K) (p : 𝓞 K)).mpr
    (Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (by simpa using hmem)))
  simpa using hlt

/-- The minus-one example now has no assumed local places. -/
theorem numberField_no_binomialPrefixDenominators_square_neg_one
    {K : Type*} [Field K] [NumberField K] (a : K) (ha : a^2 = -1) :
    ¬ BinomialPrefixDenominators a := by
  classical
  let v : ℕ → Valuation K (WithZero (Multiplicative ℤ)) := fun p =>
    if h : p.Prime then (numberField_exists_prime_place K p h).choose else (numberField_exists_prime_place K 2 Nat.prime_two).choose
  apply no_binomialPrefixDenominators_square_neg_one_of_places a ha v
  intro p hp _
  dsimp only [v]
  rw [dif_pos hp]
  exact (numberField_exists_prime_place K p hp).choose_spec

end StrictEUnit
end
