import V5BroadActualRegularity

noncomputable section
open scoped BigOperators Topology
namespace StrictEUnit

/-- An ordinary annihilator of the actual broad function produces a full
analytic family for its given minimum equation, even when that equation
has an apparent singularity at one. -/
theorem v5_actual_broad_minimal_analytic_family_at_one
    (f : ℂ → ℂ) (hf : V5IsBroadEFunction f) (hne : f ≠ 0)
    (m : ℕ) (q : ℕ → Polynomial AlgebraicComplex) (hq : q m ≠ 0)
    (hrow : ∀ z, v5RowResidual f m q z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder AlgebraicComplex f l) :
    ∃ u : Fin m → ℂ → ℂ,
      (∀ i, AnalyticAt ℂ (u i) 1) ∧ v5FiniteGermIndependent (1 : ℂ) u ∧
      ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (u i) m q z = 0 := by
  obtain ⟨n,P,hn,hP,hord⟩ := v5_actual_broad_annihilator_over_algebraic hf hne
  have hj : (P n).eval₂ (algebraMap AlgebraicComplex ℂ) 1 ≠ 0 := hord 1 one_ne_zero
  have hPne : P n ≠ 0 := fun h => hj (by rw [h,Polynomial.eval₂_zero])
  have hn' : m ≤ n := by
    by_contra! hz
    exact hmin n hz ⟨P,hPne,hP⟩
  let r := n-m
  have he : m+r = n := by dsimp [r]; omega
  have hfa (z : ℂ) : AnalyticAt ℂ f z := (hf.choose_spec.1.analyticAt z)
  obtain ⟨D,_,_,h1,u,hi,hu⟩ :=
    v5_minimal_row_family_of_ordinary_superoperator f hfa m r
      (he.symm ▸ hn) 1 P q (he.symm ▸ hj) hq
      (fun z => by rw [he]; exact hP z) hrow hmin
  exact ⟨u,fun i => (hu i).1 1 h1,hi,fun i => (hu i).2⟩

#print axioms v5_actual_broad_minimal_analytic_family_at_one
end StrictEUnit
