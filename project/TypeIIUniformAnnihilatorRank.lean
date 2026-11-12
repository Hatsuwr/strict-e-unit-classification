import DualColumnProperStableSpan
import TypeIIContactAnnihilatorContradiction
import Stage14RationalOrdinaryDerivation

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The only unproved structural input of the rank criterion: one D works for
ALL proper stable rational subspaces of the fixed dual system. -/
def UniformPolynomialDualAnnihilator
    {K : Type*} [Field K] (r : ℕ) (d : Derivation K (RatFunc K) (RatFunc K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (D : ℕ) : Prop :=
  ∀ E : Submodule (RatFunc K) (Fin r → RatFunc K), E ≠ ⊤ →
    (∀ x ∈ E, matrixDualColumn d A x ∈ E) →
    ∃ p : Fin r → Polynomial K, (∃ i, p i ≠ 0) ∧
      (∀ i, (p i).natDegree ≤ D) ∧
      ∀ x ∈ E, ∑ i, algebraMap (Polynomial K) (RatFunc K) (p i)*x i = 0

/-- Factorial division preserves independence. Only constant-field linearity
is used; the derivative is never treated as RatFunc-linear. -/
theorem divided_dual_columns_independent
    {k B : Type*} [Field k] [CharZero k] [Field B] [Algebra k B]
    {r : ℕ} (V : Module.End k (Fin r → B)) (P : Fin r → B)
    (hli : LinearIndependent B (fun j : Fin r => (V^j.val) P)) :
    LinearIndependent B (fun j : Fin r => dualDividedColumn V P j.val) := by
  classical
  let a : Fin r → B := fun j => algebraMap k B ((j.val.factorial:k)⁻¹)
  have ha (j : Fin r) : a j ≠ 0 := by
    dsimp [a]
    intro hz
    have hzero : (j.val.factorial:k)⁻¹ = 0 :=
      (algebraMap k B).injective (hz.trans (map_zero (algebraMap k B)).symm)
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hzero
  have he (j : Fin r) : dualDividedColumn V P j.val = a j • (V^j.val) P := by
    exact (IsScalarTower.algebraMap_smul B ((j.val.factorial:k)⁻¹) ((V^j.val) P)).symm
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  simp_rw [he, smul_smul] at hc
  have hz := Fintype.linearIndependent_iff.mp hli (fun j => c j*a j) hc
  intro j
  exact (mul_eq_zero.mp (hz j)).resolve_right (ha j)

/-- Formal Type-II rank from uniform bounded stable-subspace annihilators.
Z is derived by finite-jet detection before Q/P/N/M. No analyticity, PV,
regular point, f(0) nonzero, or supplied full-rank approximation is assumed. -/
theorem typeII_rank_of_uniform_polynomial_annihilator
    {K : Type*} [Field K] [CharZero K] {r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (D : ℕ) (hD : UniformPolynomialDualAnnihilator r
      stage14_rationalOrdinaryDerivation A D) :
    ∃ Z : ℕ, 0 < Z ∧ ∀ N M : ℕ, Z ≤ M →
      ∀ Q : Polynomial K, Q ≠ 0 → Q.natDegree ≤ N →
      ∀ P : Fin r → Polynomial K,
      (∀ i, seriesContact (N+M+1) ((Q : PowerSeries K)*f i-(P i : PowerSeries K))) →
      LinearIndependent (RatFunc K) (fun j : Fin r =>
        dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
          (fun i => algebraMap (Polynomial K) (RatFunc K) (P i)) j.val) := by
  obtain ⟨Z,hZ,hno⟩ := typeII_no_bounded_polynomial_annihilator f hli D
  refine ⟨Z,hZ,?_⟩
  intro N M hZM Q hQ hQN P hcontact
  apply divided_dual_columns_independent
  by_contra hdep
  obtain ⟨E,hproper,hP,hstable⟩ := dependent_dual_columns_proper_stable
    stage14_rationalOrdinaryDerivation hr A
      (fun i => algebraMap (Polynomial K) (RatFunc K) (P i)) hdep
  obtain ⟨p,hp,hdeg,hann⟩ := hD E hproper hstable
  apply hno N M hZM Q hQ hQN P hcontact p hdeg hp
  apply RatFunc.algebraMap_injective (K := K)
  simpa only [map_sum, map_mul, map_zero] using hann _ hP

end StrictEUnit
end
