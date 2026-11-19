import SameCompanionPolynomialRows
import SameCompanionScalarTuple
import OrdinaryPointJointArithmetic

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- A literal shift chain identifies every row with the corresponding iterate
of row zero; no derivative linearity or companion minimality is assumed here. -/
theorem shift_chain_iterate {R : Type*} (n : ℕ) (d : R → R)
    (v : Fin (n+1) → R)
    (hshift : ∀ i : Fin n, d (v i.castSucc) = v i.succ) :
    ∀ i : Fin (n+1), d^[i.val] (v 0) = v i := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    change d^[i.val] (v 0) = v i.castSucc at ih
    rw [Fin.val_succ, Function.iterate_succ_apply', ih]
    exact hshift i

theorem sameTuple_equation_of_shift_chain
    {K R : Type*} [Field K] [CommRing R]
    (n : ℕ) (d : R → R) (φ : Polynomial K →+* R)
    (t : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (v : Fin (n+1) → R)
    (hshift : ∀ i : Fin n, d (v i.castSucc) = v i.succ)
    (hlast : φ t * d (v (Fin.last n)) = ∑ i, φ (U (Fin.last n) i) * v i) :
    (∑ i : Fin (n+2), φ (sameCompanionScalarTuple (n+1)
      (Nat.succ_pos n) t U i) * d^[i.val] (v 0)) = 0 := by
  have hi := shift_chain_iterate n d v hshift
  have htop : d^[n+1] (v 0) = d (v (Fin.last n)) := by
    rw [Function.iterate_succ_apply']
    exact congrArg d (hi (Fin.last n))
  have hidx : (⟨(n+1)-1,by omega⟩ : Fin (n+1)) = Fin.last n := by
    apply Fin.ext
    simp
  rw [Fin.sum_univ_castSucc]
  simp only [sameCompanionScalarTuple, Fin.lastCases_castSucc, Fin.lastCases_last,
    Fin.coe_castSucc, Fin.val_last, hidx, map_neg, neg_mul]
  simp_rw [hi]
  rw [htop, Finset.sum_neg_distrib, hlast]
  exact neg_add_cancel _

/-- First-row column germs of the SAME ordinary companion have precisely
its constructed rows as their derivative jets. -/
theorem ordinaryPoint_companion_first_row_jets
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (t : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t *
        minimalDerivativeCompanion (n+1) c i l)
    (α : K) (hα : t.eval α ≠ 0) (i j : Fin (n+1)) :
    let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
    (PowerSeries.derivative K)^[i.val] (Z 0 j) = Z i j := by
  classical
  let φ := ordinaryPointPolynomialSeriesHom α
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  have htφ : φ t ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.constantCoeff K) hz
    simp only [φ, ordinaryPointPolynomialSeriesHom_apply,
      ordinaryPointPolynomialSeries_constantCoeff, map_zero] at hc
    exact hα hc
  have hs (i : Fin n) :
      PowerSeries.derivative K (Z i.castSucc j) = Z i.succ j := by
    apply mul_left_cancel₀ htφ
    calc
      φ t * PowerSeries.derivative K (Z i.castSucc j) =
          ∑ l, φ (U i.castSucc l) * Z l j :=
        ordinaryPointClearedMatrix_fundamental_cleared t U α hα i.castSucc j
      _ = φ t * Z i.succ j := by
        simp only [cleared_companion_shift_row n c t U hclear]
        rw [Finset.sum_eq_single i.succ]
        · simp [Pi.single_apply]
        · intro l hl hne
          simp [Pi.single_apply, hne, Ne.symm hne]
        · intro hn
          exact (hn (Finset.mem_univ i.succ)).elim
  exact shift_chain_iterate n (PowerSeries.derivative K) (fun i => Z i j) hs i

/-- Every constructed first-row column solves the literal TRANSLATED selected
scalar tuple. No operator is reselected, and no nonzero-constant power-series
substitution is used: only polynomials are composed with X+C alpha. -/
theorem ordinaryPoint_companion_first_row_scalar
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (t : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t *
        minimalDerivativeCompanion (n+1) c i l)
    (α : K) (hα : t.eval α ≠ 0) (j : Fin (n+1)) :
    let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
    (∑ i : Fin (n+2),
      ((sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U i).comp
        (Polynomial.X + Polynomial.C α) : PowerSeries K) *
          (PowerSeries.derivative K)^[i.val] (Z 0 j)) = 0 := by
  classical
  let φ := ordinaryPointPolynomialSeriesHom α
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  have hs (i : Fin n) : PowerSeries.derivative K (Z i.castSucc j) = Z i.succ j := by
    have ha := ordinaryPoint_companion_first_row_jets n c t U hclear α hα i.castSucc j
    have hb := ordinaryPoint_companion_first_row_jets n c t U hclear α hα i.succ j
    dsimp only at ha hb
    change (PowerSeries.derivative K)^[i.val] (Z 0 j) = Z i.castSucc j at ha
    calc
      _ = PowerSeries.derivative K ((PowerSeries.derivative K)^[i.val] (Z 0 j)) :=
        congrArg (PowerSeries.derivative K) ha.symm
      _ = (PowerSeries.derivative K)^[i.succ.val] (Z 0 j) := by
        rw [Fin.val_succ, Function.iterate_succ_apply']
      _ = _ := hb
  exact sameTuple_equation_of_shift_chain n (PowerSeries.derivative K) φ t U
    (fun i => Z i j) hs
    (ordinaryPointClearedMatrix_fundamental_cleared t U α hα (Fin.last n) j)

end StrictEUnit
end
