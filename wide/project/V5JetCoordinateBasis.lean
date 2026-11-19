import V5ShiftedAnalyticJets
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open scoped BigOperators Topology
namespace StrictEUnit

/-- Separating coordinate rows span the full finite coordinate space. -/
theorem v5_coordinate_rows_span {n : ℕ} (v : ℕ → Fin n → ℂ)
    (hsep : ∀ c : Fin n → ℂ, (∀ k, ∑ i, c i * v k i = 0) → c = 0) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro L hL
  change L = 0
  let b := Pi.basisFun ℂ (Fin n)
  have he (w : Fin n → ℂ) : L w = ∑ i, w i * L (b i) := by
    conv_lhs => rw [← b.sum_repr w]
    simp [map_sum, b, map_smul]
  have hz : (fun i => L (b i)) = 0 := hsep _ (by
    intro k
    have hh := ((Submodule.mem_dualAnnihilator L).mp hL) (v k) (Submodule.subset_span (Set.mem_range_self k))
    rw [he] at hh
    simpa only [mul_comm] using hh)
  apply LinearMap.ext
  intro w
  rw [he]
  simp [congrFun hz]

/-- A spanning sequence with nonzero row zero has a finite coordinate basis
made of its rows and retaining that row. -/
theorem v5_coordinate_basis_retaining_zero {n : ℕ} (v : ℕ → Fin n → ℂ)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) (hzero : v 0 ≠ 0) :
    ∃ b : Basis (Fin n) ℂ (Fin n → ℂ),
      (∀ i, ∃ k : ℕ, b i = v k) ∧ v 0 ∈ Set.range b := by
  classical
  have hs : LinearIndepOn ℂ id {v 0} := (linearIndepOn_singleton_iff ℂ).mpr hzero
  have hsub : ({v 0} : Set (Fin n → ℂ)) ⊆ Set.range v := by
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact Set.mem_range_self 0
  let B := Basis.extendLe hs hsub (by rw [hspan])
  letI := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card (hs.extend hsub) = n := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let e := Fintype.equivFinOfCardEq hcard
  let b := B.reindex e
  have hrange : Set.range b = Set.range B := by simp [b]
  refine ⟨b, ?_, ?_⟩
  · intro i
    have hi : b i ∈ Set.range B := hrange ▸ Set.mem_range_self i
    obtain ⟨k,hk⟩ := Basis.extendLe_subset hs hsub (by rw [hspan]) hi
    exact ⟨k,hk.symm⟩
  · rw [hrange]
    exact Basis.subset_extendLe hs hsub (by rw [hspan]) (Set.mem_singleton _)

private theorem v5_jetbasis_deriv_sum {ι : Type*}
    (u : ι → ℂ → ℂ) (x : ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) x)
    (k : ℕ) (c : ι → ℂ) (s : Finset ι) :
    iteratedDeriv k (fun z => ∑ i ∈ s, c i * u i z) x =
      ∑ i ∈ s, c i * iteratedDeriv k (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz (k : ℕ) : iteratedDeriv k (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
      induction k with
      | zero => rfl
      | succ k ih => rw [iteratedDeriv_succ, ih]; funext z; exact deriv_const z 0
    exact congrFun (hz k) x
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hfirst : ContDiffAt ℂ k (fun z => c i * u i z) x :=
      contDiffAt_const.mul (hu i).contDiffAt
    have hrest : ContDiffAt ℂ k (fun z => ∑ j ∈ s, c j * u j z) x :=
      ContDiffAt.sum fun j _ => contDiffAt_const.mul (hu j).contDiffAt
    change iteratedDeriv k ((fun z => c i * u i z) +
      (fun z => ∑ j ∈ s, c j * u j z)) x = _
    rw [iteratedDeriv_add hfirst hrest, iteratedDeriv_const_mul (hu i).contDiffAt, ih]

/-- All derivative evaluations separate an independent analytic germ family. -/
theorem v5_analytic_jet_rows_separate {n : ℕ} (u : Fin n → ℂ → ℂ) (x : ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) x) (hind : v5FiniteGermIndependent x u)
    (c : Fin n → ℂ) (hc : ∀ k, ∑ i, c i * iteratedDeriv k (u i) x = 0) : c = 0 := by
  have ha : AnalyticAt ℂ (fun z => ∑ i, c i * u i z) x :=
    Finset.analyticAt_sum _ (fun i _ => analyticAt_const.mul (hu i))
  have hd (k : ℕ) : iteratedDeriv k (fun z => ∑ i, c i * u i z) x = 0 :=
    (v5_jetbasis_deriv_sum u x hu k c Finset.univ).trans (hc k)
  have hp := ha.hasFPowerSeriesAt
  have hzero : FormalMultilinearSeries.ofScalars ℂ
      (fun k => iteratedDeriv k (fun z => ∑ i, c i * u i z) x / k.factorial) = 0 := by
    simp only [hd, zero_div]
    ext k v
    simp [FormalMultilinearSeries.ofScalars_apply_eq]
  rw [hzero] at hp
  funext i
  exact hind c hp.eventually_eq_zero i

/-- Independent analytic germs admit derivative coordinates retaining value
at the marked point whenever that evaluation functional is nonzero. -/
theorem v5_analytic_jet_coordinate_basis {n : ℕ} (u : Fin n → ℂ → ℂ) (x : ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) x) (hind : v5FiniteGermIndependent x u)
    (hvalue : ∃ i, u i x ≠ 0) :
    ∃ k : Fin n → ℕ, (∃ i, k i = 0) ∧
      ∃ b : Basis (Fin n) ℂ (Fin n → ℂ),
        ∀ i j, b i j = iteratedDeriv (k i) (u j) x := by
  classical
  let v : ℕ → Fin n → ℂ := fun k j => iteratedDeriv k (u j) x
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    v5_coordinate_rows_span v (v5_analytic_jet_rows_separate u x hu hind)
  have hv : v 0 ≠ 0 := by
    obtain ⟨i,hi⟩ := hvalue
    intro hz
    exact hi (congrFun hz i)
  obtain ⟨b,hb,hzero⟩ := v5_coordinate_basis_retaining_zero v hspan hv
  choose k hk using hb
  let q : Fin n → ℕ := fun i => if b i = v 0 then 0 else k i
  have hq (i : Fin n) : b i = v (q i) := by
    dsimp [q]
    split_ifs with h
    · exact h
    · exact hk i
  refine ⟨q, ?_, b, ?_⟩
  · obtain ⟨i,hi⟩ := hzero
    exact ⟨i, if_pos hi⟩
  · intro i j
    exact congrFun (hq i) j

/-- The chosen derivative rows form an invertible square matrix and include
order zero, not merely an arbitrary full-rank minor. -/
theorem v5_analytic_jet_det_retaining_zero {n : ℕ} (u : Fin n → ℂ → ℂ) (x : ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) x) (hind : v5FiniteGermIndependent x u)
    (hvalue : ∃ i, u i x ≠ 0) :
    ∃ k : Fin n → ℕ, (∃ i, k i = 0) ∧
      Matrix.det (fun i j : Fin n => iteratedDeriv (k i) (u j) x) ≠ 0 := by
  obtain ⟨k,hk,b,hb⟩ := v5_analytic_jet_coordinate_basis u x hu hind hvalue
  refine ⟨k,hk,?_⟩
  have he : (fun i j : Fin n => iteratedDeriv (k i) (u j) x) = b := by
    funext i j
    exact (hb i j).symm
  rw [he]
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp b.linearIndependent)).ne_zero

#print axioms v5_analytic_jet_det_retaining_zero
#print axioms v5_analytic_jet_rows_separate
#print axioms v5_analytic_jet_coordinate_basis
#print axioms v5_coordinate_rows_span
#print axioms v5_coordinate_basis_retaining_zero
end StrictEUnit
