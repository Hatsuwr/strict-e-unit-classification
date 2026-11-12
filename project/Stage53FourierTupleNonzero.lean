import FocusedFourierNormalizationCore
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Coeff

/-! NEW SOURCE-ONLY, UNCOMPILED. Nonvanishing of the literal Stage53 Fourier
polynomial tuple from any nonzero finite array. The maximal supported column
need not be the padded last column. No finite-Fuchs or corner premise is used.
The focused unified provider is imported once; no alternative Fourier model
or duplicate standalone normal-ordering provider is introduced. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- With all higher columns zero, the actual ordinary Fourier coefficient at
this column is the signed polynomial formed from that same column. -/
theorem stage53_fourierCoeff_of_columns_above_zero {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → K) (j₀ : Fin (ν + 1))
    (hzero : ∀ i j, j₀.val < j.val → A i j = 0) :
    stage53_fourierCoeff A j₀ =
      ∑ i : Fin (μ + 1), Polynomial.C ((-1 : K)^j₀.val * A i j₀) *
        Polynomial.X^i.val := by
  have hunfiltered : stage53_fourierCoeff A j₀ =
      ∑ i : Fin (μ + 1), ∑ j : Fin (ν + 1),
        Polynomial.C ((-1 : K)^j.val * A i j * (j.val.choose j₀.val : K)) *
          Polynomial.derivative^[j.val - j₀.val] (Polynomial.X^i.val) := by
    unfold stage53_fourierCoeff
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h
    · rfl
    · simp only [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h),
        Nat.cast_zero, mul_zero, map_zero, zero_mul]
  rw [hunfiltered]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j : Fin (ν + 1),
        Polynomial.C ((-1 : K)^j.val * A i j * (j.val.choose j₀.val : K)) *
          Polynomial.derivative^[j.val - j₀.val] (Polynomial.X^i.val)) =
        Polynomial.C ((-1 : K)^j₀.val * A i j₀ * (j₀.val.choose j₀.val : K)) *
          Polynomial.derivative^[j₀.val - j₀.val] (Polynomial.X^i.val) := by
      refine Finset.sum_eq_single j₀ ?_ ?_
      · intro j hj hne
        by_cases hlt : j.val < j₀.val
        · simp only [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero,
            mul_zero, map_zero, zero_mul]
        · have hneval : j.val ≠ j₀.val := fun h => hne (Fin.ext h)
          have hgt : j₀.val < j.val := by omega
          simp only [hzero i j hgt, mul_zero, zero_mul, map_zero]
      · intro h
        exact (h (Finset.mem_univ j₀)).elim
    _ = Polynomial.C ((-1 : K)^j₀.val * A i j₀) * Polynomial.X^i.val := by
      simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self,
        Function.iterate_zero_apply]

/-- Every entry of the highest supported column is recovered, with the exact
Stage53 sign, as a coefficient of the same Fourier polynomial. -/
theorem stage53_fourierCoeff_coeff_of_columns_above_zero {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → K) (j₀ : Fin (ν + 1))
    (hzero : ∀ i j, j₀.val < j.val → A i j = 0) (i₀ : Fin (μ + 1)) :
    (stage53_fourierCoeff A j₀).coeff i₀.val = (-1 : K)^j₀.val * A i₀ j₀ := by
  rw [stage53_fourierCoeff_of_columns_above_zero A j₀ hzero,
    Polynomial.finset_sum_coeff]
  calc
    (∑ i : Fin (μ + 1),
        (Polynomial.C ((-1 : K)^j₀.val * A i j₀) *
          Polynomial.X^i.val).coeff i₀.val) =
        (Polynomial.C ((-1 : K)^j₀.val * A i₀ j₀) *
          Polynomial.X^i₀.val).coeff i₀.val := by
      refine Finset.sum_eq_single i₀ ?_ ?_
      · intro i hi hne
        have hneval : i₀.val ≠ i.val := fun h => hne (Fin.ext h.symm)
        simp only [Polynomial.coeff_C_mul_X_pow, if_neg hneval]
      · intro h
        exact (h (Finset.mem_univ i₀)).elim
    _ = (-1 : K)^j₀.val * A i₀ j₀ := by
      simp only [Polynomial.coeff_C_mul_X_pow, if_pos rfl, if_true]

/-- A nonzero finite source array has a nonzero literal Fourier tuple, without
any support condition, leading-corner premise, or replacement of the array. -/
theorem stage53_fourierCoeff_exists_ne_zero {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → K) (hA : ∃ i j, A i j ≠ 0) :
    ∃ l : Fin (ν + 1), stage53_fourierCoeff A l ≠ 0 := by
  let s : Finset (Fin (ν + 1)) := Finset.univ.filter fun j => ∃ i, A i j ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, j, hij⟩ := hA
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hij⟩⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image s (fun j => j.val) hs
  obtain ⟨i₀, hi₀⟩ := (Finset.mem_filter.mp hj₀).2
  have hzero : ∀ i j, j₀.val < j.val → A i j = 0 := by
    intro i j hj
    by_contra hij
    exact (not_le_of_gt hj)
      (hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hij⟩))
  refine ⟨j₀, ?_⟩
  intro hz
  have hc := congrArg (fun p : Polynomial K => p.coeff i₀.val) hz
  change (stage53_fourierCoeff A j₀).coeff i₀.val = (0 : Polynomial K).coeff i₀.val at hc
  rw [stage53_fourierCoeff_coeff_of_columns_above_zero A j₀ hzero i₀,
    Polynomial.coeff_zero] at hc
  exact (mul_ne_zero (pow_ne_zero j₀.val (neg_ne_zero.mpr one_ne_zero)) hi₀) hc

end StrictEUnit
end
