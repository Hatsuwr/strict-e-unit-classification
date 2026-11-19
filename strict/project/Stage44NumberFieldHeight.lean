import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Normalized projective height over a fixed number field

This is a field-indexed construction using the actual infinite and finite places
of `K`. Projective scaling is proved using mathlib's product formula. No theorem
identifying heights across field extensions, or identifying this construction
with a published absolute-height convention, is assumed or asserted here.
-/

noncomputable section
open scoped BigOperators NumberField
open NumberField

namespace StrictEUnit
namespace FixedFieldHeight

variable {K I : Type*} [Field K] [NumberField K] [Fintype I] [Nonempty I]

/-- The largest coordinate absolute value at one place. -/
def localMax (v : AbsoluteValue K ℝ) (x : I → K) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => v (x i))

omit [NumberField K] in
theorem coordinate_le_localMax (v : AbsoluteValue K ℝ) (x : I → K) (i : I) :
    v (x i) ≤ localMax v x := by
  classical
  exact Finset.le_sup' (fun j => v (x j)) (Finset.mem_univ i)

omit [NumberField K] in
theorem localMax_le (v : AbsoluteValue K ℝ) (x : I → K) {B : ℝ}
    (h : ∀ i, v (x i) ≤ B) : localMax v x ≤ B := by
  classical
  exact Finset.sup'_le _ _ (fun i _ => h i)

omit [NumberField K] in
theorem localMax_nonneg (v : AbsoluteValue K ℝ) (x : I → K) :
    0 ≤ localMax v x :=
  (v.nonneg (x (Classical.arbitrary I))).trans
    (coordinate_le_localMax v x (Classical.arbitrary I))

omit [NumberField K] in
theorem localMax_pos (v : AbsoluteValue K ℝ) {x : I → K}
    (hx : ∃ i, x i ≠ 0) : 0 < localMax v x := by
  obtain ⟨i, hi⟩ := hx
  exact (v.pos_iff.mpr hi).trans_le (coordinate_le_localMax v x i)

omit [NumberField K] in
theorem localMax_mul (v : AbsoluteValue K ℝ) (a : K) (x : I → K) :
    localMax v (fun i => a * x i) = v a * localMax v x := by
  classical
  simp only [localMax, map_mul]
  exact (Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty
    (fun t : ℝ => v a * t) (fun s t => mul_max_of_nonneg s t (v.nonneg a))).symm

/-- Only nonzero coordinates enter this finite union. Zero coordinates have
absolute value zero at every place and must not contribute their infinite
multiplicative support. -/
theorem finite_localMax_mulSupport {x : I → K} (hx : ∃ i, x i ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K => localMax w.1 x).Finite := by
  classical
  let S : Set (FinitePlace K) :=
    ⋃ i : {i : I // x i ≠ 0}, Function.mulSupport (fun w : FinitePlace K => w (x i))
  have hS : S.Finite := Set.finite_iUnion fun i => FinitePlace.mulSupport_finite i.2
  apply hS.subset
  intro w hw
  by_contra hnot
  have hone (i : I) (hi : x i ≠ 0) : w (x i) = 1 := by
    by_contra hne
    exact hnot (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hne⟩)
  apply hw
  apply le_antisymm
  · apply localMax_le
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (hone i hi).le
  · obtain ⟨i, hi⟩ := hx
    have h := coordinate_le_localMax w.1 x i
    change w (x i) ≤ localMax w.1 x at h
    simpa only [hone i hi] using h

theorem log_support_finite {A : Type*} {f : A → ℝ}
    (hf : (Function.mulSupport f).Finite) :
    (Function.support fun a => Real.log (f a)).Finite := by
  apply hf.subset
  intro a ha hfa
  exact ha (by simp [hfa])

theorem log_finprod {A : Type*} (f : A → ℝ)
    (hf : (Function.mulSupport f).Finite) (hpos : ∀ a, 0 < f a) :
    Real.log (∏ᶠ a, f a) = ∑ᶠ a, Real.log (f a) := by
  classical
  rw [finprod_eq_prod f hf, Real.log_prod _ _ (fun a _ => (hpos a).ne')]
  symm
  apply finsum_eq_sum_of_support_subset
  intro a ha
  apply hf.mem_toFinset.mpr
  intro hfa
  exact ha (by simp [hfa])

/-- The additive product formula with the exact multiplicities used by
mathlib's multiplicative product formula. -/
theorem logarithmic_product_formula {a : K} (ha : a ≠ 0) :
    (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v a)) +
      (∑ᶠ w : FinitePlace K, Real.log (w a)) = 0 := by
  classical
  have hInf : 0 < ∏ v : InfinitePlace K, v a ^ v.mult :=
    Finset.prod_pos (fun v _ => pow_pos (InfinitePlace.pos_iff.mpr ha) _)
  have hFin : 0 < ∏ᶠ w : FinitePlace K, w a := by
    rw [finprod_eq_prod _ (FinitePlace.mulSupport_finite ha)]
    exact Finset.prod_pos (fun w _ => FinitePlace.pos_iff.mpr ha)
  have h := congrArg Real.log (NumberField.prod_abs_eq_one ha)
  rw [Real.log_mul hInf.ne' hFin.ne',
    Real.log_prod _ _ (fun v _ => (pow_pos (InfinitePlace.pos_iff.mpr ha) v.mult).ne'),
    log_finprod _ (FinitePlace.mulSupport_finite ha)
      (fun _ => FinitePlace.pos_iff.mpr ha), Real.log_one] at h
  simpa only [Real.log_pow] using h

/-- The sum of weighted logarithmic local maxima before degree normalization. -/
def logNumerator (x : I → K) : ℝ :=
  (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (localMax v.1 x)) +
    ∑ᶠ w : FinitePlace K, Real.log (localMax w.1 x)

/-- A normalized projective-height formula over the specified number field.
Projective statements below require a nonzero tuple. Field-extension
independence is a separate, as-yet unproved comparison. -/
def height (x : I → K) : ℝ := logNumerator x / (Module.finrank ℚ K : ℝ)

theorem finite_localMax_logSupport {x : I → K} (hx : ∃ i, x i ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (localMax w.1 x)).Finite :=
  log_support_finite (finite_localMax_mulSupport hx)

theorem logNumerator_mul (a : K) (ha : a ≠ 0) {x : I → K}
    (hx : ∃ i, x i ≠ 0) :
    logNumerator (fun i => a * x i) = logNumerator x := by
  classical
  have hInf (v : InfinitePlace K) :
      Real.log (localMax v.1 (fun i => a * x i)) =
        Real.log (v a) + Real.log (localMax v.1 x) := by
    rw [localMax_mul, Real.log_mul (v.1.pos_iff.mpr ha).ne'
      (localMax_pos v.1 hx).ne']
    rfl
  have hFin (w : FinitePlace K) :
      Real.log (localMax w.1 (fun i => a * x i)) =
        Real.log (w a) + Real.log (localMax w.1 x) := by
    rw [localMax_mul, Real.log_mul (w.1.pos_iff.mpr ha).ne'
      (localMax_pos w.1 hx).ne']
    rfl
  simp only [logNumerator, hInf, hFin, mul_add, Finset.sum_add_distrib,
    finsum_add_distrib (log_support_finite (FinitePlace.mulSupport_finite ha))
      (finite_localMax_logSupport hx)]
  linarith [logarithmic_product_formula ha]

/-- Actual projective scaling invariance, derived from the product formula. -/
theorem height_mul (a : K) (ha : a ≠ 0) {x : I → K}
    (hx : ∃ i, x i ≠ 0) : height (fun i => a * x i) = height x := by
  rw [height, logNumerator_mul a ha hx]
  rfl

theorem height_nonneg_of_coordinate_one {x : I → K} (hx : ∃ i, x i = 1) :
    0 ≤ height x := by
  obtain ⟨i, hi⟩ := hx
  have hlocal (v : AbsoluteValue K ℝ) : 1 ≤ localMax v x := by
    simpa only [hi, map_one] using coordinate_le_localMax v x i
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply add_nonneg
  · exact Finset.sum_nonneg fun v _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (hlocal v.1))
  · exact finsum_nonneg fun w => Real.log_nonneg (hlocal w.1)

theorem height_nonneg {x : I → K} (hx : ∃ i, x i ≠ 0) : 0 ≤ height x := by
  obtain ⟨i, hi⟩ := hx
  rw [← height_mul (x i)⁻¹ (inv_ne_zero hi) ⟨i, hi⟩]
  exact height_nonneg_of_coordinate_one ⟨i, inv_mul_cancel₀ hi⟩

/-- An integral element has finite-place absolute value at most one. -/
theorem finitePlace_le_one_of_integral (w : FinitePlace K) {a : K}
    (ha : IsIntegral ℤ a) : w a ≤ 1 := by
  let aInt : 𝓞 K := ⟨a, ha⟩
  simpa only [FinitePlace.norm_embedding_eq] using
    (FinitePlace.norm_le_one w.maximalIdeal aInt)

/-- For an integral tuple, the finite-place contribution is nonpositive.
It need not vanish: nonprimitive integral tuples can have negative contribution. -/
theorem finite_log_sum_nonpos_of_integral (x : I → K)
    (hint : ∀ i, IsIntegral ℤ (x i)) :
    (∑ᶠ w : FinitePlace K, Real.log (localMax w.1 x)) ≤ 0 := by
  apply finsum_induction (fun t : ℝ => t ≤ 0) le_rfl
    (fun _ _ => add_nonpos)
  intro w
  exact Real.log_nonpos (localMax_nonneg w.1 x)
    (localMax_le w.1 x (fun i => finitePlace_le_one_of_integral w (hint i)))

/-- Integral tuples with every complex conjugate bounded by `B` have
fixed-field projective height at most `log B`. -/
theorem height_le_log_of_integral (x : I → K) (hx : ∃ i, x i ≠ 0)
    (B : ℝ) (hB : 0 < B) (hint : ∀ i, IsIntegral ℤ (x i))
    (hconj : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (x i)‖ ≤ B) :
    height x ≤ Real.log B := by
  classical
  have hInf (v : InfinitePlace K) : localMax v.1 x ≤ B := by
    apply localMax_le
    intro i
    simpa only [RingHom.toRatAlgHom_apply, InfinitePlace.norm_embedding_eq]
      using hconj v.embedding.toRatAlgHom i
  have hdegree : 0 < (Module.finrank ℚ K : ℝ) :=
    Nat.cast_pos.mpr Module.finrank_pos
  apply (div_le_iff₀ hdegree).mpr
  have hbound : (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (localMax v.1 x)) ≤
      (Module.finrank ℚ K : ℝ) * Real.log B := by
    calc
      _ ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log B :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
          ((Real.log_le_log_iff (localMax_pos v.1 hx) hB).mpr (hInf v)) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  have hfinite := finite_log_sum_nonpos_of_integral x hint
  dsimp [logNumerator]
  linarith

/-- The leading-one vector. Its index type is nonempty even when `I` is empty. -/
def affineTuple {J : Type*} (x : J → K) : Option J → K := fun o => o.elim 1 x

/-- A common positive integer denominator and a bound on every conjugate imply
an actual normalized fixed-field height estimate. -/
theorem affine_height_le {J : Type*} [Fintype J] (x : J → K)
    (d : ℕ) (hd : 0 < d) (B : ℝ) (hB : 1 ≤ B)
    (hint : ∀ i, IsIntegral ℤ ((d : K) * x i))
    (hconj : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (x i)‖ ≤ B) :
    height (affineTuple x) ≤ Real.log (d : ℝ) + Real.log B := by
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let y : Option J → K := fun i => (d : K) * affineTuple x i
  have hy : ∃ i, y i ≠ 0 := ⟨none, by simpa [y, affineTuple] using hdK⟩
  have hyInt : ∀ i, IsIntegral ℤ (y i) := by
    intro i
    cases i with
    | none =>
      simp only [y, affineTuple, Option.elim_none, mul_one]
      exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := K) (x := (d : ℤ)))
    | some i => exact hint i
  have hyConj (σ : K →ₐ[ℚ] ℂ) (i : Option J) : ‖σ (y i)‖ ≤ (d : ℝ) * B := by
    cases i with
    | none =>
      simp only [y, affineTuple, Option.elim_none, mul_one, map_natCast, Complex.norm_natCast]
      exact le_mul_of_one_le_right hdR.le hB
    | some i =>
      simpa only [y, affineTuple, Option.elim_some, map_mul, map_natCast, norm_mul,
        Complex.norm_natCast] using mul_le_mul_of_nonneg_left (hconj σ i) hdR.le
  have h := height_le_log_of_integral y hy ((d : ℝ) * B)
    (mul_pos hdR hBpos) hyInt hyConj
  have hscale : height y = height (affineTuple x) :=
    height_mul (d : K) hdK ⟨none, by simp [affineTuple]⟩
  rw [hscale, Real.log_mul hdR.ne' hBpos.ne'] at h
  exact h

end FixedFieldHeight
end StrictEUnit
