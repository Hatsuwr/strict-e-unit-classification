import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Denominator-free reverse jet transport for multiplication by 1-z.
The input is the triangular product-rule identity. -/
namespace StrictEUnit

open scoped BigOperators

def v5ReverseJetRow {R : Type*} [CommRing R] (t : R) : ℕ → ℕ → R
  | 0, l => if l = 0 then 1 else 0
  | j + 1, l => (if l = j + 1 then t ^ (j + 1) else 0) +
      ((j + 1 : ℕ) : R) * v5ReverseJetRow t j l

theorem v5_reverseJetRow_above {R : Type*} [CommRing R] (t : R)
    {j l : ℕ} (h : j < l) : v5ReverseJetRow t j l = 0 := by
  induction j with
  | zero => simp [v5ReverseJetRow, Nat.ne_of_gt h]
  | succ j ih =>
    simp [v5ReverseJetRow, Nat.ne_of_gt h, ih (Nat.lt_trans (Nat.lt_succ_self j) h)]

theorem v5_reverseJetRow_diag {R : Type*} [CommRing R] (t : R) (j : ℕ) :
    v5ReverseJetRow t j j = t ^ j := by
  cases j with
  | zero => simp [v5ReverseJetRow]
  | succ j => simp [v5ReverseJetRow, v5_reverseJetRow_above t (Nat.lt_succ_self j)]

theorem v5_reverseJetRow_eval {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : R) (F G : ℕ → S)
    (h0 : F 0 = φ t * G 0)
    (hs : ∀ j, F (j + 1) = φ t * G (j + 1) - ((j + 1 : ℕ) : S) * G j)
    (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    (∑ l ∈ Finset.range (m + 1), φ (v5ReverseJetRow t j l) * F l) =
      (φ t) ^ (j + 1) * G j := by
  classical
  induction j with
  | zero =>
    simp [v5ReverseJetRow, apply_ite φ, ite_mul, Finset.sum_ite_eq', h0]
  | succ j ih =>
    have hj' : j ≤ m := Nat.le_trans (Nat.le_succ j) hj
    have hm : j + 1 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    simp only [v5ReverseJetRow, map_add, map_mul, map_natCast, apply_ite φ,
      map_pow, map_zero, add_mul, Finset.sum_add_distrib, ite_mul,
      zero_mul, Finset.sum_ite_eq', if_pos hm]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    rw [ih hj', hs, pow_succ' (φ t) (j + 1)]
    ring

def v5ReverseAnnihilator {R : Type*} [CommRing R]
    (t : R) (m : ℕ) (a : ℕ → R) (l : ℕ) : R :=
  ∑ j ∈ Finset.range (m + 1), a j * t ^ (m - j) * v5ReverseJetRow t j l

theorem v5_reverseAnnihilator_top {R : Type*} [CommRing R]
    (t : R) (m : ℕ) (a : ℕ → R) :
    v5ReverseAnnihilator t m a m = a m * t ^ m := by
  classical
  unfold v5ReverseAnnihilator
  rw [Finset.sum_eq_single m]
  · simp [v5_reverseJetRow_diag]
  · intro j hj hne
    have hlt : j < m := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hne
    rw [v5_reverseJetRow_above t hlt, mul_zero]
  · simp

theorem v5_reverseAnnihilator_eval {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : R) (F G : ℕ → S)
    (h0 : F 0 = φ t * G 0)
    (hs : ∀ j, F (j + 1) = φ t * G (j + 1) - ((j + 1 : ℕ) : S) * G j)
    (m : ℕ) (a : ℕ → R) :
    (∑ l ∈ Finset.range (m + 1), φ (v5ReverseAnnihilator t m a l) * F l) =
      (φ t) ^ (m + 1) * (∑ j ∈ Finset.range (m + 1), φ (a j) * G j) := by
  classical
  simp only [v5ReverseAnnihilator, map_sum, Finset.sum_mul, map_mul, map_pow]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ = (φ (a j) * φ t ^ (m - j)) *
        (∑ l ∈ Finset.range (m + 1), φ (v5ReverseJetRow t j l) * F l) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ = _ := by
      rw [v5_reverseJetRow_eval φ t F G h0 hs m hj']
      have hp : (φ t) ^ (m - j) * (φ t) ^ (j + 1) = (φ t) ^ (m + 1) := by
        rw [← pow_add, ← Nat.add_assoc, Nat.sub_add_cancel hj']
      calc
        _ = (φ t ^ (m - j) * φ t ^ (j + 1)) * (φ (a j) * G j) := by ring
        _ = _ := by rw [hp]

theorem v5_reverseAnnihilator_top_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (t : R) (m : ℕ) (a : ℕ → R) (ht : t ≠ 0) (ha : a m ≠ 0) :
    v5ReverseAnnihilator t m a m ≠ 0 := by
  rw [v5_reverseAnnihilator_top]
  exact mul_ne_zero ha (pow_ne_zero m ht)

#print axioms v5_reverseJetRow_eval
#print axioms v5_reverseAnnihilator_eval
#print axioms v5_reverseAnnihilator_top_ne_zero

end StrictEUnit

/-! The affine product rule near an analytic center. -/
namespace StrictEUnit

open scoped Topology BigOperators

private theorem v5_hasDerivAt_affine (z : ℂ) :
    HasDerivAt (fun w : ℂ => 1 - w) (-1) z :=
  (hasDerivAt_id z).const_sub 1

private theorem v5_hasDerivAt_iterated {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (n : ℕ) :
    HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g z) z := by
  rw [iteratedDeriv_succ]
  rw [iteratedDeriv_eq_iterate]
  exact (hg.iterated_deriv n).differentiableAt.hasDerivAt

theorem v5_affine_iteratedDeriv_succ_eventually {g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z => (1 - z) * g z) =ᶠ[𝓝 x]
      (fun z => (1 - z) * iteratedDeriv (n + 1) g z -
        ((n + 1 : ℕ) : ℂ) * iteratedDeriv n g z) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_succ]
    simp only [iteratedDeriv_zero, Nat.zero_add, Nat.cast_one, one_mul]
    filter_upwards [hg.eventually_analyticAt] with z hz
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    have hd := ((v5_hasDerivAt_affine z).mul hz.differentiableAt.hasDerivAt).deriv
    rw [hd]
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ]
    filter_upwards [ih.deriv, hg.eventually_analyticAt] with z he hz
    rw [he]
    have hd := (((v5_hasDerivAt_affine z).mul (v5_hasDerivAt_iterated hz (n + 1))).sub
      ((v5_hasDerivAt_iterated hz n).const_mul ((n + 1 : ℕ) : ℂ))).deriv
    rw [hd]
    push_cast
    ring

theorem v5_affine_iteratedDeriv_succ {g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z => (1 - z) * g z) x =
      (1 - x) * iteratedDeriv (n + 1) g x -
        ((n + 1 : ℕ) : ℂ) * iteratedDeriv n g x :=
  (v5_affine_iteratedDeriv_succ_eventually hg n).self_of_nhds

#print axioms v5_affine_iteratedDeriv_succ_eventually
#print axioms v5_affine_iteratedDeriv_succ
end StrictEUnit
namespace StrictEUnit
open scoped BigOperators

def v5ForwardAnnihilator {R : Type*} [CommRing R]
    (t : R) (m : ℕ) (a : ℕ → R) (j : ℕ) : R :=
  t * a j - (if j < m then ((j + 1 : ℕ) : R) * a (j + 1) else 0)

theorem v5_forwardAnnihilator_eval {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : R) (F G : ℕ → S)
    (h0 : F 0 = φ t * G 0)
    (hs : ∀ j, F (j + 1) = φ t * G (j + 1) - ((j + 1 : ℕ) : S) * G j)
    (m : ℕ) (a : ℕ → R) :
    (∑ j ∈ Finset.range (m + 1), φ (v5ForwardAnnihilator t m a j) * G j) =
      ∑ j ∈ Finset.range (m + 1), φ (a j) * F j := by
  have hc :
      (∑ j ∈ Finset.range (m + 1),
        φ (if j < m then ((j + 1 : ℕ) : R) * a (j + 1) else 0) * G j) =
      ∑ j ∈ Finset.range m, φ (a (j + 1)) * (((j + 1 : ℕ) : S) * G j) := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, if_false, map_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (Finset.mem_range.mp hj), map_mul, map_natCast]
    ring
  have hl :
      (∑ j ∈ Finset.range (m + 1), φ (a j) * (φ t * G j)) =
      (∑ j ∈ Finset.range m, φ (a (j + 1)) * (φ t * G (j + 1))) +
        φ (a 0) * (φ t * G 0) := Finset.sum_range_succ' _ _
  have hf :
      (∑ j ∈ Finset.range (m + 1), φ (a j) * F j) =
      (∑ j ∈ Finset.range m, φ (a (j + 1)) * F (j + 1)) + φ (a 0) * F 0 :=
    Finset.sum_range_succ' _ _
  rw [hf, h0]
  simp only [v5ForwardAnnihilator, map_sub, sub_mul, Finset.sum_sub_distrib,
    hs, mul_sub]
  rw [hc]
  have he : (∑ j ∈ Finset.range (m + 1), φ (t * a j) * G j) =
      ∑ j ∈ Finset.range (m + 1), φ (a j) * (φ t * G j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    ring
  rw [he, hl]
  ring

def v5HasAnnihilatorOrder (K : Type*) [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (m : ℕ) : Prop :=
  ∃ a : ℕ → Polynomial K, a m ≠ 0 ∧
    ∀ z : ℂ, (∑ j ∈ Finset.range (m + 1),
      (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (a j) * iteratedDeriv j f z) = 0

theorem v5_affine_hasAnnihilatorOrder_iff {K : Type*} [Field K] [Algebra K ℂ]
    {g : ℂ → ℂ} (hg : ∀ z, AnalyticAt ℂ g z) (m : ℕ) :
    v5HasAnnihilatorOrder K (fun z => (1 - z) * g z) m ↔
      v5HasAnnihilatorOrder K g m := by
  let t : Polynomial K := 1 - Polynomial.X
  have ht : t ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial K => p.coeff 1) h
    simpa [t, Polynomial.coeff_one] using hc
  have hφ (z : ℂ) : (Polynomial.eval₂RingHom (algebraMap K ℂ) z) t = 1 - z := by
    simp [t]
  have h0 (z : ℂ) :
      iteratedDeriv 0 (fun z => (1 - z) * g z) z =
      (Polynomial.eval₂RingHom (algebraMap K ℂ) z) t * iteratedDeriv 0 g z := by
    simp [hφ, iteratedDeriv_zero]
  have hs (z : ℂ) (j : ℕ) :
      iteratedDeriv (j + 1) (fun z => (1 - z) * g z) z =
      (Polynomial.eval₂RingHom (algebraMap K ℂ) z) t * iteratedDeriv (j + 1) g z -
        ((j + 1 : ℕ) : ℂ) * iteratedDeriv j g z := by
    rw [hφ]
    exact v5_affine_iteratedDeriv_succ (hg z) j
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨v5ForwardAnnihilator t m a, ?_, ?_⟩
    · simpa [v5ForwardAnnihilator] using mul_ne_zero ht ha
    · intro z
      rw [v5_forwardAnnihilator_eval _ t (fun j => iteratedDeriv j (fun w => (1 - w) * g w) z)
        (fun j => iteratedDeriv j g z) (h0 z) (hs z) m a]
      exact h z
  · rintro ⟨a, ha, h⟩
    refine ⟨v5ReverseAnnihilator t m a, v5_reverseAnnihilator_top_ne_zero t m a ht ha, ?_⟩
    intro z
    rw [v5_reverseAnnihilator_eval _ t (fun j => iteratedDeriv j (fun w => (1 - w) * g w) z)
        (fun j => iteratedDeriv j g z) (h0 z) (hs z) m a, h z, mul_zero]

def v5HasMinimalAnnihilatorOrder (K : Type*) [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (m : ℕ) : Prop :=
  v5HasAnnihilatorOrder K f m ∧ ∀ n < m, ¬ v5HasAnnihilatorOrder K f n

theorem v5_affine_minimalAnnihilatorOrder_iff {K : Type*} [Field K] [Algebra K ℂ]
    {g : ℂ → ℂ} (hg : ∀ z, AnalyticAt ℂ g z) (m : ℕ) :
    v5HasMinimalAnnihilatorOrder K (fun z => (1 - z) * g z) m ↔
      v5HasMinimalAnnihilatorOrder K g m := by
  constructor <;> rintro ⟨hm, hlt⟩
  · exact ⟨(v5_affine_hasAnnihilatorOrder_iff hg m).mp hm,
      fun n hn h => hlt n hn ((v5_affine_hasAnnihilatorOrder_iff hg n).mpr h)⟩
  · exact ⟨(v5_affine_hasAnnihilatorOrder_iff hg m).mpr hm,
      fun n hn h => hlt n hn ((v5_affine_hasAnnihilatorOrder_iff hg n).mp h)⟩

#print axioms v5_forwardAnnihilator_eval
#print axioms v5_affine_hasAnnihilatorOrder_iff
#print axioms v5_affine_minimalAnnihilatorOrder_iff
end StrictEUnit
