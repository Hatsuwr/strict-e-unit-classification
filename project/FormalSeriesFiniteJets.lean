import FiniteCoefficientDetection
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Push

/-!
NEW SOURCE-ONLY: literal coefficient jets on finite-dimensional subspaces of
ordinary power series and Laurent series. No differential equation, analytic
convergence, finite series support, or characteristic-zero premise is used.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {K : Type*} [Field K]

/-- Initial ordinary coefficients detect every member of a finite-dimensional
subspace. Separation is proved from PowerSeries.ext, not assumed. -/
theorem powerSeries_subspace_finite_jet
    (S : Submodule K (PowerSeries K)) [FiniteDimensional K S] :
    ∃ N : ℕ, 0 < N ∧ ∀ f : PowerSeries K, f ∈ S →
      (∀ n < N, PowerSeries.coeff K n f = 0) → f = 0 := by
  let c (n : ℕ) : S →ₗ[K] K := (PowerSeries.coeff K n).comp S.subtype
  have hsep (x : S) (hx : ∀ n, c n x = 0) : x = 0 := by
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    exact (hx n).trans (map_zero (PowerSeries.coeff K n)).symm
  obtain ⟨N, hN, hdet⟩ := exists_initial_linearForm_detection c hsep
  refine ⟨N, hN, fun f hf hz => ?_⟩
  exact congrArg Subtype.val (hdet ⟨f, hf⟩ hz)

/-- A finite independent ordinary-series family remains independent after
truncating its literal coefficients to some finite initial segment. -/
theorem powerSeries_family_finite_jet_linearIndependent
    {I : Type*} [Fintype I] (f : I → PowerSeries K)
    (hli : LinearIndependent K f) :
    ∃ N : ℕ, 0 < N ∧ LinearIndependent K
      (fun i (n : Fin N) => PowerSeries.coeff K n.val (f i)) := by
  classical
  let S : Submodule K (PowerSeries K) := Submodule.span K (Set.range f)
  letI : FiniteDimensional K S :=
    FiniteDimensional.span_of_finite K (Set.finite_range f)
  obtain ⟨N, hN, hdet⟩ := powerSeries_subspace_finite_jet S
  refine ⟨N, hN, Fintype.linearIndependent_iff.2 ?_⟩
  intro a ha
  apply Fintype.linearIndependent_iff.1 hli a
  apply hdet
  · exact Submodule.sum_mem S (fun i _ =>
      S.smul_mem (a i) (Submodule.subset_span ⟨i, rfl⟩))
  · intro n hn
    have h := congrFun ha (⟨n, hn⟩ : Fin N)
    simpa only [map_sum, PowerSeries.coeff_smul, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply] using h

/-- A finite-dimensional ordinary-series subspace has uniformly bounded order
on its NONZERO elements. Zero is not given a finite order bound. -/
theorem powerSeries_subspace_order_bound
    (S : Submodule K (PowerSeries K)) [FiniteDimensional K S] :
    ∃ N : ℕ, 0 < N ∧ ∀ f : PowerSeries K, f ∈ S → f ≠ 0 →
      ∃ n < N, PowerSeries.coeff K n f ≠ 0 ∧ f.order ≤ (n : ℕ∞) := by
  classical
  obtain ⟨N, hN, hdet⟩ := powerSeries_subspace_finite_jet S
  refine ⟨N, hN, fun f hf hne => ?_⟩
  have hex : ∃ n < N, PowerSeries.coeff K n f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (hdet f hf h)
  obtain ⟨n, hn, hc⟩ := hex
  exact ⟨n, hn, hc, PowerSeries.order_le n hc⟩

/-- Literal Laurent coefficient extraction with the coefficientwise scalar
action actually selected by the standard Laurent-series module instance. -/
def finiteJet_laurentCoeff (n : ℤ) : LaurentSeries K →ₗ[K] K where
  toFun f := f.coeff n
  map_add' f g := HahnSeries.coeff_add
  map_smul' c f := by
    exact HahnSeries.coeff_smul

/-- Finitely many actual integer-indexed coefficients detect a Laurent
subspace; no common lower support bound is supplied as a premise. -/
theorem laurentSeries_subspace_finite_coefficients
    (S : Submodule K (LaurentSeries K)) [FiniteDimensional K S] :
    ∃ s : Finset ℤ, ∀ f : LaurentSeries K, f ∈ S →
      (∀ n ∈ s, f.coeff n = 0) → f = 0 := by
  let c (n : ℤ) : S →ₗ[K] K := (finiteJet_laurentCoeff n).comp S.subtype
  have hsep (x : S) (hx : ∀ n, c n x = 0) : x = 0 := by
    apply Subtype.ext
    apply HahnSeries.ext
    funext n
    exact (hx n).trans HahnSeries.coeff_zero.symm
  obtain ⟨s, hdet⟩ := exists_finset_linearForm_detection c hsep
  refine ⟨s, fun f hf hz => ?_⟩
  exact congrArg Subtype.val (hdet ⟨f, hf⟩ hz)

/-- A finite independent Laurent family has a finite coefficient projection
which is independent. Negative exponents are retained, not discarded. -/
theorem laurentSeries_family_finite_coefficients_linearIndependent
    {I : Type*} [Fintype I] (f : I → LaurentSeries K)
    (hli : LinearIndependent K f) :
    ∃ s : Finset ℤ, LinearIndependent K
      (fun i (n : s) => (f i).coeff n.val) := by
  classical
  let S : Submodule K (LaurentSeries K) := Submodule.span K (Set.range f)
  letI : FiniteDimensional K S :=
    FiniteDimensional.span_of_finite K (Set.finite_range f)
  obtain ⟨s, hdet⟩ := laurentSeries_subspace_finite_coefficients S
  refine ⟨s, Fintype.linearIndependent_iff.2 ?_⟩
  intro a ha
  apply Fintype.linearIndependent_iff.1 hli a
  apply hdet
  · exact Submodule.sum_mem S (fun i _ =>
      S.smul_mem (a i) (Submodule.subset_span ⟨i, rfl⟩))
  · intro n hn
    have h := congrFun ha (⟨n, hn⟩ : s)
    change finiteJet_laurentCoeff n (∑ i, a i • f i) = 0
    simpa only [map_sum, map_smul, finiteJet_laurentCoeff,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using h

/-- Uniform upper order bound for nonzero Laurent members. The finite detecting
set may include negative exponents, and the subspace may be zero. -/
theorem laurentSeries_subspace_order_bound
    (S : Submodule K (LaurentSeries K)) [FiniteDimensional K S] :
    ∃ N : ℕ, 0 < N ∧ ∀ f : LaurentSeries K, f ∈ S → f ≠ 0 →
      ∃ n : ℤ, n < (N : ℤ) ∧ f.coeff n ≠ 0 ∧ f.order ≤ n := by
  classical
  obtain ⟨s, hdet⟩ := laurentSeries_subspace_finite_coefficients S
  refine ⟨s.sup Int.toNat + 1, Nat.succ_pos _, fun f hf hne => ?_⟩
  have hex : ∃ n ∈ s, f.coeff n ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (hdet f hf h)
  obtain ⟨n, hn, hc⟩ := hex
  have hnle : n.toNat ≤ s.sup Int.toNat := Finset.le_sup (f := Int.toNat) hn
  have hcast : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n
  refine ⟨n, ?_, hc, HahnSeries.order_le_of_coeff_ne_zero hc⟩
  exact lt_of_le_of_lt hcast (Int.ofNat_lt.mpr (Nat.lt_succ_of_le hnle))

end StrictEUnit
end
