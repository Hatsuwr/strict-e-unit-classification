import IdealNormCoprimeProducts
import SupermultiplicativeEulerBound

noncomputable section
open scoped NumberField Topology nonZeroDivisors BigOperators
open NumberField Finset
namespace StrictEUnit

theorem idealNormCoefficient_one (K : Type*) [Field K] [NumberField K] :
    idealNormCoefficient K 1 = 1 := by
  letI : Unique {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = 1} :=
    { default := ⟨1, by change Ideal.absNorm 1 = 1; exact map_one _⟩
      uniq := by
        intro I
        apply Subtype.ext
        apply Subtype.ext
        change (I.val : Ideal (𝓞 K)) = 1
        simpa only [Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp I.prop }
  exact Nat.card_unique

def idealNormRealTerm (K : Type*) [Field K] [NumberField K] (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (idealNormCoefficient K n : ℝ) / (n : ℝ)^s

theorem idealNormRealTerm_nonneg (K : Type*) [Field K] [NumberField K] (s : ℝ) (n : ℕ) :
    0 ≤ idealNormRealTerm K s n := by
  unfold idealNormRealTerm
  split_ifs <;> positivity

theorem idealNormRealTerm_complex (K : Type*) [Field K] [NumberField K] (s : ℝ) (n : ℕ) :
    (idealNormRealTerm K s n : ℂ) =
      LSeries.term (fun n => (idealNormCoefficient K n : ℂ)) (s : ℂ) n := by
  simp only [idealNormRealTerm, LSeries.term]
  split_ifs
  · simp
  · rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp

theorem idealNormRealTerm_summable (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : Summable (idealNormRealTerm K s) := by
  have h := (idealNormLSeries_summable K (s := (s : ℂ)) (by simpa using hs)).norm
  simpa only [← idealNormRealTerm_complex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (idealNormRealTerm_nonneg K s _)] using h

theorem idealNormRealTerm_one (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    idealNormRealTerm K s 1 = 1 := by
  simp [idealNormRealTerm, idealNormCoefficient_one]

theorem idealNormRealTerm_coprime_supermultiplicative
    (K : Type*) [Field K] [NumberField K] (s : ℝ) {m n : ℕ} (h : m.Coprime n) :
    idealNormRealTerm K s m * idealNormRealTerm K s n ≤ idealNormRealTerm K s (m*n) := by
  by_cases hm : m = 0
  · simp [hm, idealNormRealTerm]
  by_cases hn : n = 0
  · simp [hn, idealNormRealTerm]
  simp only [idealNormRealTerm, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn), Nat.cast_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), ← mul_div_mul_comm]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast idealNormCoefficient_coprime_supermultiplicative K h
  · positivity

theorem idealNormRealTerm_tsum_eq_norm (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (∑' n, idealNormRealTerm K s n) = ‖idealNormLSeries K (s : ℂ)‖ := by
  have he : (((∑' n, idealNormRealTerm K s n) : ℝ) : ℂ) = idealNormLSeries K (s : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (idealNormRealTerm_complex K s)
  rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (tsum_nonneg (idealNormRealTerm_nonneg K s))]

theorem idealNormLSeries_finite_euler_lower
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) (S : Finset ℕ) :
    ∏ p ∈ S with p.Prime, (∑' e : ℕ, idealNormRealTerm K s (p^e)) ≤
      ‖idealNormLSeries K (s : ℂ)‖ := by
  rw [← idealNormRealTerm_tsum_eq_norm K hs]
  exact supermultiplicative_euler_finite_bound_total (idealNormRealTerm_nonneg K s)
    (idealNormRealTerm_one K s) (idealNormRealTerm_coprime_supermultiplicative K s)
    (idealNormRealTerm_summable K hs) S

end StrictEUnit
end
