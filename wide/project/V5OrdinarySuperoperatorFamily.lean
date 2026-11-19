import V5PolynomialPseudoDivisionCore
import V5OrdinaryScalarFamily

namespace StrictEUnit
open scoped BigOperators Topology
open Filter

/-- Construct a simultaneous analytic frame from a positive-order polynomial
row over any coefficient field embedded in ℂ. -/
theorem v5_ordinary_scalar_family_on_ball {K : Type*} [Field K] [Algebra K ℂ]
    (n : ℕ) (hn : 0 < n) (p : ℕ → Polynomial K) (x : ℂ)
    (hp : (p n).eval₂ (algebraMap K ℂ) x ≠ 0) :
    ∃ D : Set ℂ, IsOpen D ∧ IsPreconnected D ∧ x ∈ D ∧
      ∃ u : Fin n → ℂ → ℂ, v5FiniteGermIndependent x u ∧
        (∀ j, AnalyticOnNhd ℂ (u j) D) ∧
        ∀ j z, z ∈ D → v5RowResidual (u j) n p z = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let P := fun k => (p k).map (algebraMap K ℂ)
  have hp' : (P (r+1)).eval x ≠ 0 := by simpa only [P, Polynomial.eval_map] using hp
  obtain ⟨u, ha, _, hind, he⟩ := v5_ordinary_scalar_family r P x hp'
  obtain ⟨D, ho, hc, hx, han, hz⟩ := v5_scalar_family_common_ball P u ha he
  refine ⟨D, ho, hc, hx, u, hind, han, ?_⟩
  intro j z hzD
  have hh := hz j z hzD
  change (∑ k ∈ Finset.range (r+1+1), (P k).eval z * iteratedDeriv k (u j) z) = 0 at hh
  change (∑ k ∈ Finset.range (r+1+1), (p k).eval₂ (algebraMap K ℂ) z *
    iteratedDeriv k (u j) z) = 0
  simpa only [P, Polynomial.eval_map] using hh

/-- Even if the minimal row is singular at x, an ordinary polynomial
superoperator at x supplies an independent local solution family for it.
There is no supplied factorization or auxiliary point in the premise. -/
theorem v5_minimal_row_family_of_ordinary_superoperator {K : Type*} [Field K] [Algebra K ℂ]
    (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (m r : ℕ) (hn : 0 < m+r) (x : ℂ)
    (p q : ℕ → Polynomial K)
    (hp : (p (m+r)).eval₂ (algebraMap K ℂ) x ≠ 0) (hq : q m ≠ 0)
    (hp0 : ∀ z, v5RowResidual f (m+r) p z = 0)
    (hq0 : ∀ z, v5RowResidual f m q z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder K f l) :
    ∃ D : Set ℂ, IsOpen D ∧ IsPreconnected D ∧ x ∈ D ∧
      ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent x v ∧
        ∀ i, AnalyticOnNhd ℂ (v i) D ∧
          ∀ᶠ z in 𝓝 x, v5RowResidual (v i) m q z = 0 := by
  have hp' : p (m+r) ≠ 0 := by
    intro h
    exact hp (by rw [h, Polynomial.eval₂_zero])
  obtain ⟨b, hb, hfactor⟩ := v5_minimal_polynomial_right_factor f hf m r p q hp' hq hp0 hq0 hmin
  obtain ⟨D, ho, hpre, hx, u, hind, hu, he⟩ :=
    v5_ordinary_scalar_family_on_ball (m+r) hn p x hp
  refine ⟨D, ho, hpre, hx, ?_⟩
  have hsub : m+r-m = r := by omega
  have hl : ∀ j z, z ∈ D → v5RowResidual (v5RowResidual (u j) m q) r b z = 0 := by
    intro j z hz
    rw [v5_polynomialRows_compose_action b q r m ho (hu j) hz]
    have hscale : v5RowResidual (u j) (m+r) (v5ComposePolynomialRows b q r m) z =
        (Polynomial.eval₂RingHom (algebraMap K ℂ) z) ((q m)^(r+1)) *
          v5RowResidual (u j) (m+r) p z := by
      unfold v5RowResidual
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      rw [hfactor k (by omega), map_mul, mul_assoc]
    rw [hscale, he j z hz, mul_zero]
  apply v5_extract_right_factor_family_off_exceptional (n := m+r) (m := m)
    (by omega) ho hpre hx u hu hind q (1 : Polynomial ℂ) (1 : Polynomial ℂ)
    one_ne_zero one_ne_zero b (by simpa only [hsub] using hb)
  intro j z hz _ _
  simpa only [hsub, Polynomial.eval_one, div_one] using hl j z hz

#print axioms v5_ordinary_scalar_family_on_ball
#print axioms v5_minimal_row_family_of_ordinary_superoperator
/-- An ordinary annihilator of the divided entire function forces a full
family for any chosen minimal row of the original affine product, and
every member of that family vanishes at 1. -/
theorem v5_norm_vanishing_family_of_ordinary_superoperator {K : Type*} [Field K] [Algebra K ℂ]
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (n m : ℕ) (hn : 0 < n)
    (p a : ℕ → Polynomial K)
    (hp : (p n).eval₂ (algebraMap K ℂ) 1 ≠ 0) (ha : a m ≠ 0)
    (hp0 : ∀ z, v5RowResidual g n p z = 0)
    (ha0 : ∀ z, v5RowResidual (fun w => (1-w)*g w) m a z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder K (fun w => (1-w)*g w) l) :
    ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent 1 v ∧
      ∀ i, AnalyticAt ℂ (v i) 1 ∧ v i 1 = 0 ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (v i) m a z = 0 := by
  have hminA : v5HasMinimalAnnihilatorOrder K (fun w => (1-w)*g w) m :=
    ⟨⟨a, ha, ha0⟩, hmin⟩
  obtain ⟨⟨q, hq, hq0⟩, hminG⟩ := (v5_affine_minimalAnnihilatorOrder_iff hg m).mp hminA
  have hp' : p n ≠ 0 := by
    intro h
    exact hp (by rw [h, Polynomial.eval₂_zero])
  have hmn : m ≤ n := by
    by_contra! h
    exact hminG n h ⟨p, hp', hp0⟩
  have hsum : m+(n-m) = n := by omega
  obtain ⟨D, _, _, h1, u, hind, hu⟩ :=
    v5_minimal_row_family_of_ordinary_superoperator g hg m (n-m)
      (by simpa only [hsum] using hn) 1 p q (by simpa only [hsum] using hp) hq
      (by simpa only [hsum] using hp0) hq0 hminG
  exact v5_norm_vanishing_family_of_quotient hg (fun i => (hu i).1 1 h1)
    m a q ha hq hmin ha0 hq0 (fun i => (hu i).2) hind

#print axioms v5_norm_vanishing_family_of_ordinary_superoperator
end StrictEUnit
