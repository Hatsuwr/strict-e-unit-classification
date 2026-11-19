import V5OrdinarySystemColumns
import V5OrdinaryScalarUniqueness

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

/-- The coordinate chain of a scalar companion system records successive jets. -/
theorem v5_companion_chain_jets {r : ℕ} {x : ℂ}
    (U : Fin (r+1) → ℂ → ℂ)
    (hnext : ∀ (k : ℕ) (hk : k < r),
      deriv (U ⟨k, by omega⟩) =ᶠ[𝓝 x] U ⟨k+1, by omega⟩) :
    ∀ (k : ℕ) (hk : k < r+1),
      iteratedDeriv k (U 0) =ᶠ[𝓝 x] U ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [iteratedDeriv_succ]
    exact (ih (by omega)).deriv.trans (hnext k (by omega))

/-- At an ordinary point a positive-order complex polynomial scalar row has
a full normalized family of analytic solution germs. -/
theorem v5_ordinary_scalar_family (r : ℕ) (p : ℕ → Polynomial ℂ)
    (x : ℂ) (hp : (p (r+1)).eval x ≠ 0) :
    ∃ u : Fin (r+1) → ℂ → ℂ,
      (∀ j, AnalyticAt ℂ (u j) x) ∧
      (∀ j k : Fin (r+1), iteratedDeriv k.val (u j) x = if k = j then 1 else 0) ∧
      v5FiniteGermIndependent x u ∧
      ∀ j, ∀ᶠ z in 𝓝 x, v5RowResidual (u j) (r+1) p z = 0 := by
  classical
  let t := p (r+1)
  let P : Matrix (Fin (r+1)) (Fin (r+1)) (Polynomial ℂ) :=
    fun k l => if k.val = r then -p l.val else if l.val = k.val+1 then t else 0
  obtain ⟨hA, U, hu, h0, hsys⟩ := v5_ordinary_rational_system_columns t P x hp
  let u : Fin (r+1) → ℂ → ℂ := fun j => U j 0
  have ht : ∀ᶠ z in 𝓝 x, t.eval z ≠ 0 := t.continuousAt.eventually_ne hp
  have hchain (j : Fin (r+1)) (k : ℕ) (hk : k < r) :
      deriv (U j ⟨k, by omega⟩) =ᶠ[𝓝 x] U j ⟨k+1, by omega⟩ := by
    filter_upwards [hsys j ⟨k, by omega⟩, ht] with z hz htz
    rw [hz]
    have hn : k ≠ r := by omega
    have hnxt : k+1 < r+1 := by omega
    let next : Fin (r+1) := ⟨k+1, hnxt⟩
    have he (l : Fin (r+1)) : l.val = k+1 ↔ l = next := by
      change l.val = next.val ↔ l = next
      exact ⟨Fin.ext, fun h => congrArg Fin.val h⟩
    simp only [P, hn, if_false, he]
    rw [Finset.sum_eq_single next]
    · simp [htz, next]
    · intro l _ hne
      simp [hne]
    · simp
  have hjets (j : Fin (r+1)) (k : Fin (r+1)) :
      iteratedDeriv k.val (u j) =ᶠ[𝓝 x] U j k :=
    v5_companion_chain_jets (U j) (hchain j) k.val k.isLt
  refine ⟨u, fun j => hu j 0, ?_, ?_, ?_⟩
  · intro j k
    exact (hjets j k).eq_of_nhds.trans (h0 j k)
  · apply v5_cyclic_coordinate_germ_independent 0 U
      (fun i k _ => if k = i then 1 else 0) hu h0
    · intro j i
      simpa using hjets j i
    · apply Filter.Eventually.frequently
      filter_upwards [] with z
      intro v w hv
      funext i
      simpa using congrFun hv i
  · intro j
    have htop := (hjets j ⟨r, by omega⟩).deriv
    have hall := Filter.eventually_all.mpr (hjets j)
    filter_upwards [htop, hsys j ⟨r, by omega⟩, hall, ht] with z hz hs hjs htz
    have hder : iteratedDeriv (r+1) (u j) z =
        ∑ l : Fin (r+1), (t.eval z)⁻¹ * (-(p l.val).eval z) * U j l z := by
      rw [iteratedDeriv_succ]
      rw [hz, hs]
      simp [P]
    change (∑ k ∈ Finset.range (r+1+1), (p k).eval₂ (algebraMap ℂ ℂ) z *
      iteratedDeriv k (u j) z) = 0
    change (∑ k ∈ Finset.range (r+1+1), (p k).eval z * iteratedDeriv k (u j) z) = 0
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
    simp_rw [hjs]
    rw [hder, Finset.mul_sum]
    have hterm (l : Fin (r+1)) :
        t.eval z * ((t.eval z)⁻¹ * (-(p l.val).eval z) * U j l z) =
        -((p l.val).eval z * U j l z) := by
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ htz, one_mul, neg_mul]
    change (∑ l : Fin (r+1), (p l.val).eval z * U j l z) +
      (∑ l : Fin (r+1), t.eval z * ((t.eval z)⁻¹ * (-(p l.val).eval z) * U j l z)) = 0
    simp only [hterm, Finset.sum_neg_distrib, add_neg_cancel]

/-- A finite family of analytic solution germs has a common open connected
ball on which all its equations hold pointwise. -/
theorem v5_scalar_family_common_ball {n : ℕ} {x : ℂ}
    (p : ℕ → Polynomial ℂ) (u : Fin n → ℂ → ℂ)
    (hu : ∀ j, AnalyticAt ℂ (u j) x)
    (he : ∀ j, ∀ᶠ z in 𝓝 x, v5RowResidual (u j) n p z = 0) :
    ∃ D : Set ℂ, IsOpen D ∧ IsPreconnected D ∧ x ∈ D ∧
      (∀ j, AnalyticOnNhd ℂ (u j) D) ∧
      ∀ j z, z ∈ D → v5RowResidual (u j) n p z = 0 := by
  have h : ∀ᶠ z in 𝓝 x, ∀ j, AnalyticAt ℂ (u j) z ∧ v5RowResidual (u j) n p z = 0 :=
    Filter.eventually_all.mpr fun j => (hu j).eventually_analyticAt.and (he j)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨Metric.ball x ε, Metric.isOpen_ball, (convex_ball x ε).isPreconnected,
    Metric.mem_ball_self hε, ?_, ?_⟩
  · intro j z hz
    exact (hball z hz j).1
  · intro j z hz
    exact (hball z hz j).2

#print axioms v5_scalar_family_common_ball
#print axioms v5_companion_chain_jets
#print axioms v5_ordinary_scalar_family
end StrictEUnit
