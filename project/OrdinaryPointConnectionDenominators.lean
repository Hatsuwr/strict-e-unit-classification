import IntegralNormHouse
import PolynomialConnectionClearing
import Stage26FiniteCoefficientField
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Denominators of the SAME evaluated divided-connection expressions at a
constructed integer ordinary point. No identification with fundamental-matrix
coefficients or full E-arithmetic solution family is asserted here. -/
noncomputable section
open scoped NumberField BigOperators Matrix
namespace StrictEUnit

theorem ordinaryJet_natCast_integral {K : Type*} [Field K] (n : ℕ) :
    IsIntegral ℤ (n : K) := by
  exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := K) (x := (n : ℤ)))

theorem ordinaryJet_integral_cleared_eval {K : Type*} [Field K]
    (P : Polynomial K) (δ a : ℕ)
    (hP : ∀ l, IsIntegral ℤ ((δ:K) * P.coeff l)) :
    IsIntegral ℤ ((δ:K) * P.eval (a:K)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply IsIntegral.sum
  intro l hl
  convert (hP l).mul ((ordinaryJet_natCast_integral (K := K) a).pow l) using 1 <;> ring

theorem ordinaryJet_norm_power_clearing
    {K : Type*} [Field K] [NumberField K]
    (v : 𝓞 K) (hv : v ≠ 0) (δ s m : ℕ) (hms : m ≤ s)
    (x : K) (hx : IsIntegral ℤ ((δ:K)*x)) :
    let q := Int.natAbs (Algebra.norm ℤ v)
    IsIntegral ℤ (((δ*q^s:ℕ):K)*x/(v:K)^m) := by
  let q := Int.natAbs (Algebra.norm ℤ v)
  change IsIntegral ℤ (((δ*q^s:ℕ):K)*x/(v:K)^m)
  obtain ⟨w,hw⟩ := (ringOfIntegers_natAbs_norm_certificate v hv).2.2
  have hq : (q:K) = (v:K)*(w:K) := by
    simpa only [q, map_natCast, map_mul] using congrArg (algebraMap (𝓞 K) K) hw
  have hvK : (v:K) ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact hz
  have hpow : (q:K)^s = (q:K)^m*(q:K)^(s-m) := by
    have he : m+(s-m)=s := by omega
    rw [← pow_add, he]
  have hqm : (q:K)^m = (v:K)^m*(w:K)^m := by
    rw [hq,mul_pow]
  have heq : (((δ*q^s:ℕ):K)*x/(v:K)^m) =
      (((δ:K)*x)*(w:K)^m)*(q:K)^(s-m) := by
    apply (div_eq_iff (pow_ne_zero m hvK)).2
    simp only [Nat.cast_mul,Nat.cast_pow]
    rw [hpow,hqm]
    ring
  rw [heq]
  exact (hx.mul ((NumberField.RingOfIntegers.isIntegral_coe w).pow m)).mul
    ((ordinaryJet_natCast_integral (K := K) q).pow (s-m))

theorem ordinaryJet_cutoff_norm_bound (q δ s : ℕ) (hq : 0 < q)
    (E : ℝ) (hE : 1 ≤ E) (hδ : (δ:ℝ) ≤ E^(s+1)) :
    ((δ*q^s:ℕ):ℝ) ≤ ((q:ℝ)*E)^(s+1) := by
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  have hE0 : (0:ℝ) ≤ E := le_trans zero_le_one hE
  have hpow : (q:ℝ)^s ≤ (q:ℝ)^(s+1) := by
    rw [pow_succ]
    calc
      (q:ℝ)^s = (q:ℝ)^s*1 := (mul_one _).symm
      _ ≤ (q:ℝ)^s*(q:ℝ) := mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 s)
  rw [Nat.cast_mul,Nat.cast_pow,mul_pow]
  calc
    (δ:ℝ)*(q:ℝ)^s ≤ E^(s+1)*(q:ℝ)^s :=
      mul_le_mul_of_nonneg_right hδ (pow_nonneg hq0 s)
    _ ≤ E^(s+1)*(q:ℝ)^(s+1) :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hE0 (s+1))
    _ = (q:ℝ)^(s+1)*E^(s+1) := mul_comm _ _

theorem ordinaryJet_same_cutoff_eval_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (H : ℕ → Matrix (Fin r) (Fin r) (Polynomial K))
    (a : ℕ) (v : 𝓞 K) (hv : v ≠ 0) (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ, ∃ δ : ℕ, 0 < δ ∧ (δ:ℝ) ≤ E^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(H m i j).coeff l)) :
    let q := Int.natAbs (Algebra.norm ℤ v)
    0 < q ∧ 1 ≤ (q:ℝ)*E ∧
    ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r,
        IsIntegral ℤ ((d:K)*(H m i j).eval (a:K)/(v:K)^m) := by
  let q := Int.natAbs (Algebra.norm ℤ v)
  have hq : 0 < q := (ringOfIntegers_natAbs_norm_certificate v hv).1
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hD : 1 ≤ (q:ℝ)*E := by
    simpa only [one_mul] using (mul_le_mul hq1 hE zero_le_one (Nat.cast_nonneg q))
  refine ⟨hq,hD,?_⟩
  intro s
  obtain ⟨δ,hδ,hδbound,hδint⟩ := hden s
  refine ⟨δ*q^s,Nat.mul_pos hδ (pow_pos hq s),
    ordinaryJet_cutoff_norm_bound q δ s hq E hE hδbound,?_⟩
  intro m hm i j
  exact ordinaryJet_norm_power_clearing v hv δ s m hm ((H m i j).eval (a:K))
    (ordinaryJet_integral_cleared_eval (H m i j) δ a (hδint m hm i j))

theorem same_integral_clearing_ordinary_point_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ, ∃ δ : ℕ, 0 < δ ∧ (δ:ℝ) ≤ E^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K)))
          m i j).coeff l)) :
    ∃ a : ℕ, (T.map (algebraMap (𝓞 K) K)).eval (a:K) ≠ 0 ∧
      let v := T.eval (a : 𝓞 K)
      let q := Int.natAbs (Algebra.norm ℤ v)
      0 < q ∧ 1 ≤ (q:ℝ)*E ∧
      ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
        ∀ m, m ≤ s → ∀ i j : Fin r,
          IsIntegral ℤ ((d:K) *
            (dividedPolynomialConnectionSequence
              (T.map (algebraMap (𝓞 K) K))
              (Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K)))
              m i j).eval (a:K) /
            ((T.map (algebraMap (𝓞 K) K)).eval (a:K))^m) := by
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  obtain ⟨a,ha⟩ := stage26_polynomial_eventually_nat_nonzero t hT
  let v : 𝓞 K := T.eval (a : 𝓞 K)
  have hvmap : (v:K) = t.eval (a:K) := by
    dsimp only [v,t]
    rw [Polynomial.eval_map]
    simpa only [map_natCast] using
      (Polynomial.eval₂_at_apply (p := T) (algebraMap (𝓞 K) K) (a : 𝓞 K)).symm
  have hvK : (v:K) ≠ 0 := by
    rw [hvmap]
    exact ha a le_rfl
  have hv : v ≠ 0 := by
    intro hz
    apply hvK
    exact congrArg (fun z : 𝓞 K => (z:K)) hz
  refine ⟨a,ha a le_rfl,?_⟩
  have h := ordinaryJet_same_cutoff_eval_denominators
    (fun m => dividedPolynomialConnectionSequence t U m) a v hv E hE hden
  simpa only [hvmap] using h

end StrictEUnit
end
