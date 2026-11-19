import OrdinaryPointCompanionScalarFamily
import SelectedScalarFieldMapTransport

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

theorem linearIndependent_of_kronecker_functionals
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (f : ι → V) (J : ι → V →ₗ[K] K)
    (hJ : ∀ i j, J i (f j) = if i = j then 1 else 0) :
    LinearIndependent K f := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (J i) hc
  simpa only [map_sum, map_smul, hJ, map_zero, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] using h

theorem powerSeries_linearIndependent_of_derivative_jets
    {K : Type*} [Field K] {r : ℕ} (f : Fin r → PowerSeries K)
    (hjet : ∀ i j : Fin r,
      PowerSeries.constantCoeff K ((PowerSeries.derivative K)^[i.val] (f j)) =
        if i = j then 1 else 0) :
    LinearIndependent K f := by
  classical
  let D : Module.End K (PowerSeries K) := (PowerSeries.derivative K).toLinearMap
  let J : Fin r → PowerSeries K →ₗ[K] K :=
    fun i => (PowerSeries.coeff K 0).comp (D ^ i.val)
  apply linearIndependent_of_kronecker_functionals f J
  intro i j
  change PowerSeries.coeff K 0 ((D ^ i.val) (f j)) = _
  rw [Module.End.pow_apply, PowerSeries.coeff_zero_eq_constantCoeff]
  exact hjet i j

/-- Independence after coefficient extension is proved again from the literal
jets, rather than silently extending scalar independence. -/
theorem powerSeries_map_linearIndependent_of_derivative_jets
    {K L : Type*} [Field K] [Field L] {r : ℕ}
    (φ : K →+* L) (f : Fin r → PowerSeries K)
    (hjet : ∀ i j : Fin r,
      PowerSeries.constantCoeff K ((PowerSeries.derivative K)^[i.val] (f j)) =
        if i = j then 1 else 0) :
    LinearIndependent L (fun j => PowerSeries.map φ (f j)) := by
  apply powerSeries_linearIndependent_of_derivative_jets
  intro i j
  rw [← ordinaryBorel_map_iterate_derivative]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hjet i j]
  split_ifs <;> simp

theorem ordinaryPoint_companion_first_row_jet_values
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (t : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t *
        minimalDerivativeCompanion (n+1) c i l)
    (α : K) (hα : t.eval α ≠ 0) (i j : Fin (n+1)) :
    let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
    PowerSeries.constantCoeff K ((PowerSeries.derivative K)^[i.val] (Z 0 j)) =
      if i = j then 1 else 0 := by
  dsimp only
  rw [ordinaryPoint_companion_first_row_jets n c t U hclear α hα i j]
  simpa only [Matrix.map_apply, Matrix.one_apply] using congrArg
    (fun M : Matrix (Fin (n+1)) (Fin (n+1)) K => M i j)
    (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U α))

theorem ordinaryPoint_companion_first_row_linearIndependent
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (t : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t *
        minimalDerivativeCompanion (n+1) c i l)
    (α : K) (hα : t.eval α ≠ 0) :
    LinearIndependent K (fun j : Fin (n+1) =>
      formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) 0 j) := by
  apply powerSeries_linearIndependent_of_derivative_jets
  exact ordinaryPoint_companion_first_row_jet_values n c t U hclear α hα

theorem ordinaryPoint_companion_first_row_map_linearIndependent
    {K L : Type*} [Field K] [CharZero K] [Field L]
    (φ : K →+* L) (n : ℕ) (c : Fin (n+1) → RatFunc K) (t : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t *
        minimalDerivativeCompanion (n+1) c i l)
    (α : K) (hα : t.eval α ≠ 0) :
    LinearIndependent L (fun j : Fin (n+1) => PowerSeries.map φ
      (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) 0 j)) := by
  apply powerSeries_map_linearIndependent_of_derivative_jets
  exact ordinaryPoint_companion_first_row_jet_values n c t U hclear α hα

end StrictEUnit
end
