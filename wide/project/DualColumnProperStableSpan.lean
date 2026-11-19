import MatrixDualBinomial
import CovariantRowStabilization

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Exact transpose/sign bridge. No coefficient-field linearity of d. -/
theorem matrixDualColumn_eq_covariant {k B : Type*} [Field k] [Field B] [Algebra k B]
    (d : Derivation k B B) {r : ℕ} (A : Matrix (Fin r) (Fin r) B) :
    (matrixDualColumn d A : (Fin r → B) → (Fin r → B)) =
      rationalCovariantRow d (fun i j => -A j i) := by
  funext x j
  change d (x j) - ∑ i, A j i*x i = d (x j) + ∑ i, x i*(-A j i)
  simp only [mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- Dependence before dimension r gives a proper stable subspace containing
exactly the original seed. Zero seed is included, with E=bottom. -/
theorem dependent_dual_columns_proper_stable
    {k B : Type*} [Field k] [Field B] [Algebra k B]
    (d : Derivation k B B) {r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin r) (Fin r) B) (P : Fin r → B)
    (hdep : ¬ LinearIndependent B
      (fun i : Fin r => ((matrixDualColumn d A)^i.val) P)) :
    ∃ E : Submodule B (Fin r → B), E ≠ ⊤ ∧ P ∈ E ∧
      ∀ x ∈ E, matrixDualColumn d A x ∈ E := by
  classical
  let D := rationalCovariantRow d (fun i j => -A j i)
  have heq : (matrixDualColumn d A : (Fin r → B) → (Fin r → B)) = D :=
    matrixDualColumn_eq_covariant d A
  by_cases hp : P = 0
  · refine ⟨⊥, ?_, by simp [hp], ?_⟩
    · intro h
      have hdim := congrArg (fun S : Submodule B (Fin r → B) => Module.finrank B S) h
      simp only [finrank_bot, finrank_top, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hdim
      omega
    · intro x hx
      have hx0 : x = 0 := by simpa only [Submodule.mem_bot] using hx
      simp [hx0]
  have hdep' : ¬ LinearIndependent B (fun i : Fin ((r-1)+1) => (D^[i.val]) P) := by
    have hdim : r-1+1 = r := Nat.sub_add_cancel hr
    rw [hdim]
    simpa only [Module.End.pow_apply, heq] using hdep
  obtain ⟨s, hs, hli, hnext⟩ :=
    FirstDependence.exists_independent_prefix_of_dependent (fun n => (D^[n]) P) (r-1) hdep'
  have hpos : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hp ((FirstDependence.first_dependence_zero_iff
      (fun n => (D^[n]) P) s hli hnext).mp hz)
  let E := Submodule.span B (Set.range (fun i : Fin s => (D^[i.val]) P))
  have hdim : Module.finrank B E = s := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  refine ⟨E, ?_, Submodule.subset_span ⟨⟨0,hpos⟩,rfl⟩, ?_⟩
  · intro htop
    rw [htop] at hdim
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    omega
  · intro x hx
    rw [heq]
    exact rationalCovariantRow_initial_span_stable d (fun i j => -A j i) P s hnext x hx

end StrictEUnit
end
