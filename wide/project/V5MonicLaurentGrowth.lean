import V5MonicRootBound
import V5LaurentExtraction

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Uniform Laurent envelope in any radius dominating both t and its inverse. -/
theorem v5_laurent_radius_envelope {k : Type*} [CommRing k] (ι : k →+* ℂ)
    (L : LaurentPolynomial k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (t : ℂˣ) (r : ℝ),
      1 ≤ r → ‖(t : ℂ)‖ ≤ r → ‖(t : ℂ)⁻¹‖ ≤ r →
      ‖LaurentPolynomial.eval₂ ι t L‖ ≤ C * r ^ N := by
  induction L using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C, hC, m, hp⟩ := hp
    obtain ⟨D, hD, n, hq⟩ := hq
    refine ⟨C + D, add_nonneg hC hD, m + n, ?_⟩
    intro t r hr ht hi
    have hm : r ^ m ≤ r ^ (m+n) := pow_le_pow_right₀ hr (Nat.le_add_right m n)
    have hn : r ^ n ≤ r ^ (m+n) := pow_le_pow_right₀ hr (Nat.le_add_left n m)
    calc
      ‖LaurentPolynomial.eval₂ ι t (p+q)‖ ≤
          ‖LaurentPolynomial.eval₂ ι t p‖ + ‖LaurentPolynomial.eval₂ ι t q‖ := by
        rw [map_add]; exact norm_add_le _ _
      _ ≤ C * r ^ m + D * r ^ n := add_le_add (hp t r hr ht hi) (hq t r hr ht hi)
      _ ≤ C * r ^ (m+n) + D * r ^ (m+n) :=
        add_le_add (mul_le_mul_of_nonneg_left hm hC) (mul_le_mul_of_nonneg_left hn hD)
      _ = (C+D) * r ^ (m+n) := by ring
  | C_mul_T n a =>
    refine ⟨‖ι a‖, norm_nonneg _, n.natAbs, ?_⟩
    intro t r hr ht hi
    rw [LaurentPolynomial.eval₂_C_mul_T, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    cases n with
    | ofNat n =>
      simpa using pow_le_pow_left₀ (norm_nonneg (t : ℂ)) ht n
    | negSucc n =>
      simpa [zpow_negSucc, norm_inv, norm_pow, inv_pow] using
        pow_le_pow_left₀ (norm_nonneg ((t : ℂ)⁻¹)) hi (n+1)

theorem v5_laurent_sum_radius_envelope {k α : Type*} [CommRing k]
    (ι : k →+* ℂ) (L : α → LaurentPolynomial k) (s : Finset α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (t : ℂˣ) (r : ℝ),
      1 ≤ r → ‖(t : ℂ)‖ ≤ r → ‖(t : ℂ)⁻¹‖ ≤ r →
      (∑ i ∈ s, ‖LaurentPolynomial.eval₂ ι t (L i)‖) ≤ C * r ^ N := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert a s ha hs =>
    obtain ⟨C, hC, m, hp⟩ := v5_laurent_radius_envelope ι (L a)
    obtain ⟨D, hD, n, hq⟩ := hs
    refine ⟨C+D, add_nonneg hC hD, m+n, ?_⟩
    intro t r hr ht hi
    rw [Finset.sum_insert ha]
    have hm : r ^ m ≤ r ^ (m+n) := pow_le_pow_right₀ hr (Nat.le_add_right m n)
    have hn : r ^ n ≤ r ^ (m+n) := pow_le_pow_right₀ hr (Nat.le_add_left n m)
    calc
      _ ≤ C * r^m + D * r^n := add_le_add (hp t r hr ht hi) (hq t r hr ht hi)
      _ ≤ C * r^(m+n) + D * r^(m+n) :=
        add_le_add (mul_le_mul_of_nonneg_left hm hC) (mul_le_mul_of_nonneg_left hn hD)
      _ = (C+D) * r^(m+n) := by ring

/-- The monic Laurent equation alone gives a uniform polynomial radial envelope. -/
theorem v5_monic_laurent_root_radius_envelope {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (t : ℂˣ) (z : ℂ) (r : ℝ),
      (p.map (LaurentPolynomial.eval₂ ι (t^q))).IsRoot z →
      1 ≤ r → ‖(t : ℂ)‖ ≤ r → ‖(t : ℂ)⁻¹‖ ≤ r → ‖z‖ ≤ C * r^N := by
  obtain ⟨C, hC, N, hN⟩ := v5_laurent_sum_radius_envelope ι p.coeff (Finset.range p.natDegree)
  refine ⟨1+C, by positivity, q*N, ?_⟩
  intro t z r hz hr ht hi
  have htq : ‖((t^q : ℂˣ) : ℂ)‖ ≤ r^q := by
    simpa using pow_le_pow_left₀ (norm_nonneg (t : ℂ)) ht q
  have hiq : ‖((t^q : ℂˣ) : ℂ)⁻¹‖ ≤ r^q := by
    simpa [norm_pow, norm_inv, inv_pow] using pow_le_pow_left₀ (norm_nonneg ((t : ℂ)⁻¹)) hi q
  have hh := hN (t^q) (r^q) (one_le_pow₀ hr) htq hiq
  rw [← pow_mul] at hh
  calc
    ‖z‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree,
        ‖LaurentPolynomial.eval₂ ι (t^q) (p.coeff i)‖ :=
      v5_monic_laurent_kummer_root_norm_bound ι t q hp hz
    _ ≤ 1 + C * r^(q*N) := add_le_add_left hh 1
    _ ≤ r^(q*N) + C * r^(q*N) := add_le_add_right (one_le_pow₀ hr) _
    _ = (1+C) * r^(q*N) := by ring

/-- Explicit two-ended growth follows without any analytic hypothesis. -/
theorem v5_monic_laurent_function_growth {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic)
    (q : ℕ) (f : ℂ → ℂ)
    (heq : ∀ t : ℂˣ, (p.map (LaurentPolynomial.eval₂ ι (t^q))).IsRoot (f t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      (∀ z ≠ 0, ‖z‖ < 1 → ‖f z‖ ≤ C / ‖z‖^N) ∧
      (∀ z, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^N) := by
  obtain ⟨C, hC, N, hN⟩ := v5_monic_laurent_root_radius_envelope ι hp q
  refine ⟨C, hC, N, ?_, ?_⟩
  · intro z hz hzn
    let t := Units.mk0 z hz
    have hr : 1 ≤ ‖z‖⁻¹ := (one_le_inv₀ (norm_pos_iff.mpr hz)).mpr hzn.le
    have hh := hN t (f z) ‖z‖⁻¹ (heq t) hr (hzn.le.trans hr) (by simp [t])
    simpa [inv_pow, div_eq_mul_inv] using hh
  · intro z hz
    have hz0 : z ≠ 0 := by intro hh; norm_num [hh] at hz
    let t := Units.mk0 z hz0
    have hi : ‖z⁻¹‖ ≤ ‖z‖ := by
      rw [norm_inv]
      exact ((inv_le_one₀ (norm_pos_iff.mpr hz0)).mpr hz).trans hz
    exact hN t (f z) ‖z‖ (heq t) hz le_rfl hi

/-- Weighted form directly matches the analytic and arithmetic extraction interfaces. -/
theorem v5_monic_laurent_function_weighted_growth {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic)
    (q : ℕ) (f : ℂ → ℂ)
    (heq : ∀ t : ℂˣ, (p.map (LaurentPolynomial.eval₂ ι (t^q))).IsRoot (f t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ,
      (∀ z ≠ 0, ‖z‖ < 1 → ‖z^m * f z‖ ≤ C) ∧
      (∀ z, 1 ≤ ‖z‖ → ‖z^m * f z‖ ≤ C * ‖z‖^(m+m)) := by
  obtain ⟨C, hC, m, hz, hi⟩ := v5_monic_laurent_function_growth ι hp q f heq
  refine ⟨C, hC, m, ?_, ?_⟩
  · intro z hn hzn
    rw [norm_mul, norm_pow]
    have hh := mul_le_mul_of_nonneg_left (hz z hn hzn) (pow_nonneg (norm_nonneg z) m)
    simpa [mul_div_cancel₀ _ (pow_ne_zero m (norm_ne_zero_iff.mpr hn))] using hh
  · intro z hn
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖z‖^m * (C * ‖z‖^m) := mul_le_mul_of_nonneg_left (hi z hn) (pow_nonneg (norm_nonneg z) m)
      _ = C * ‖z‖^(m+m) := by rw [pow_add]; ring

/-- Analytic roots on the punctured plane of a fixed monic Laurent equation are finite Laurent. -/
theorem v5_laurent_of_monic_laurent_equation {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic)
    (q : ℕ) (f : ℂ → ℂ) (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (heq : ∀ t : ℂˣ, (p.map (LaurentPolynomial.eval₂ ι (t^q))).IsRoot (f t)) :
    ∃ L : LaurentPolynomial ℂ, ∀ z : ℂˣ,
      LaurentPolynomial.eval₂ (RingHom.id ℂ) z L = f z := by
  obtain ⟨C, hC, N, hz, hi⟩ := v5_monic_laurent_function_growth ι hp q f heq
  exact v5_laurent_of_two_ended_growth N N hf C C hC hz hi

end StrictEUnit
#print axioms StrictEUnit.v5_laurent_radius_envelope

#print axioms StrictEUnit.v5_laurent_sum_radius_envelope
#print axioms StrictEUnit.v5_monic_laurent_root_radius_envelope

#print axioms StrictEUnit.v5_monic_laurent_function_growth
#print axioms StrictEUnit.v5_monic_laurent_function_weighted_growth
#print axioms StrictEUnit.v5_laurent_of_monic_laurent_equation
