import Mathlib.Analysis.Meromorphic.Order
import ElementaryGeneratorGrowth

/-! Actual removal of the order at the origin. The local nonzero analytic
factor is obtained from mathlib's meromorphic-order theorem, not assumed.
The original function's arbitrary total-function value at zero is ignored:
all original-function factorization identities are stated only off zero. -/
noncomputable section
open Filter
open scoped Topology
namespace StrictEUnit

/-- A meromorphic function nonzero on the punctured plane has finite order
at the origin. This excludes the identically-zero germ case. -/
theorem meromorphic_origin_order_ne_top {v : ℂ → ℂ}
    (hm : MeromorphicAt v 0) (hnz : ∀ z, z ≠ 0 → v z ≠ 0) : hm.order ≠ ⊤ := by
  intro htop
  have hz := hm.order_eq_top_iff.mp htop
  have hn : ∀ᶠ z in 𝓝[≠] (0 : ℂ), v z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hnz z hz
  obtain ⟨z, hz, hn⟩ := (hz.and hn).exists
  exact hn hz

/-- Remove the actual meromorphic order at zero. The resulting global
function is entire and nowhere zero, and agrees with z^(-q)*v away from zero. -/
theorem exists_entire_nonzero_remove_origin {v : ℂ → ℂ}
    (hm : MeromorphicAt v 0)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℂ v z)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0) :
    ∃ q : ℤ, ∃ w : ℂ → ℂ,
      hm.order = (q : WithTop ℤ) ∧ Differentiable ℂ w ∧
      (∀ z, w z ≠ 0) ∧ (∀ z, z ≠ 0 → w z = z^(-q) * v z) ∧
      (∀ z, z ≠ 0 → v z = z^q * w z) := by
  classical
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (meromorphic_origin_order_ne_top hm hnz)
  obtain ⟨g, hg, hg0, he⟩ := hm.order_eq_int_iff.mp hq.symm
  let w : ℂ → ℂ := fun z => if z = 0 then g 0 else z^(-q) * v z
  have hw_off (z : ℂ) (hz : z ≠ 0) : w z = z^(-q) * v z := if_neg hz
  have hw_near : w =ᶠ[𝓝 (0 : ℂ)] g := by
    rw [eventually_nhdsWithin_iff] at he
    filter_upwards [he] with z hez
    by_cases hz : z = 0
    · simp only [w, hz, if_pos rfl]
    · rw [hw_off z hz, hez hz]
      simp only [sub_zero, smul_eq_mul]
      rw [← mul_assoc, ← zpow_add₀ hz, neg_add_cancel, zpow_zero, one_mul]
  refine ⟨q, w, hq.symm, ?_, ?_, hw_off, ?_⟩
  · intro z
    by_cases hz : z = 0
    · subst z
      exact (hg.congr hw_near.symm).differentiableAt
    · have hp : DifferentiableAt ℂ (fun y : ℂ => y^(-q) * v y) z :=
        (analyticAt_id.zpow hz).differentiableAt.mul (hd z hz)
      apply hp.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with y hy
      exact hw_off y hy
  · intro z
    by_cases hz : z = 0
    · simpa only [w, hz, if_pos rfl] using hg0
    · rw [hw_off z hz]
      exact mul_ne_zero (zpow_ne_zero _ hz) (hnz z hz)
  · intro z hz
    rw [hw_off z hz, ← mul_assoc, ← zpow_add₀ hz, add_neg_cancel, zpow_zero, one_mul]

end StrictEUnit
#print axioms StrictEUnit.meromorphic_origin_order_ne_top
#print axioms StrictEUnit.exists_entire_nonzero_remove_origin
