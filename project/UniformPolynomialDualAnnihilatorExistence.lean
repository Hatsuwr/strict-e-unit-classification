import UniformRationalCovariantChart
import BoundedChartPolynomialAnnihilator
import TypeIIUniformAnnihilatorRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Discharge the uniform stable-subspace annihilator premise of the formal
Type-II rank criterion. The fixed chart bound is chosen before E; clearing
one nonpivot row produces a polynomial annihilator of degree at most r*D.
Properness implies strict dimension, including the vacuous r=0 case.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Every fixed rational connection admits one polynomial annihilator-degree
bound for all its proper invariant rational subspaces. No bounded chart or
annihilator premise is supplied. -/
theorem exists_uniform_polynomial_dual_annihilator
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) :
    ∃ D : ℕ, UniformPolynomialDualAnnihilator r
      stage14_rationalOrdinaryDerivation A D := by
  classical
  obtain ⟨D, hD⟩ := exists_uniform_rational_covariant_chart_bound A
  refine ⟨r * D, ?_⟩
  intro E hproper hstable
  have hstable' : ∀ v : Fin r → RatFunc K, v ∈ E →
      ((fun i => stage14_rationalOrdinaryDerivation (v i)) - A *ᵥ v) ∈ E := by
    intro v hv
    exact hstable v hv
  obtain ⟨s, hs, hdim, p, b, hpivot, hspan, hdegree⟩ := hD E hstable'
  have hsr : s < r := by
    rw [hdim]
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      (Submodule.finrank_lt hproper)
  let B : Matrix (Fin r) (Fin s) (RatFunc K) :=
    Matrix.of (fun i j => (b j : Fin r → RatFunc K) i)
  have hspanB : Submodule.span (RatFunc K)
      (Set.range (fun j : Fin s => fun i : Fin r => B i j)) = E := hspan
  obtain ⟨a, ha, hdeg, hann⟩ :=
    exists_polynomial_annihilator_of_normalized_chart_span hsr B p hpivot hdegree
  refine ⟨a, ha, ?_, ?_⟩
  · intro i
    exact (hdeg i).trans (Nat.mul_le_mul_right D hs)
  · intro x hx
    apply hann x
    rw [hspanB]
    exact hx

/-- Eventual Type-II rank for the actual divided dual iterates of one fixed
system. The threshold precedes Q/P/N/M. The only family hypothesis is actual
RatFunc-linear independence of the literal Laurent embeddings of f. -/
theorem typeII_eventual_divided_dual_rank
    {K : Type*} [Field K] [CharZero K] {r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (hli : LinearIndependent (RatFunc K)
      (fun i => HahnSeries.ofPowerSeries ℤ K (f i))) :
    ∃ Z : ℕ, 0 < Z ∧ ∀ N M : ℕ, Z ≤ M →
      ∀ Q : Polynomial K, Q ≠ 0 → Q.natDegree ≤ N →
      ∀ P : Fin r → Polynomial K,
      (∀ i, seriesContact (N+M+1)
        ((Q : PowerSeries K) * f i - (P i : PowerSeries K))) →
      LinearIndependent (RatFunc K) (fun j : Fin r =>
        dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
          (fun i => algebraMap (Polynomial K) (RatFunc K) (P i)) j.val) := by
  obtain ⟨D, hD⟩ := exists_uniform_polynomial_dual_annihilator A
  exact typeII_rank_of_uniform_polynomial_annihilator hr A f hli D hD

end StrictEUnit
end
