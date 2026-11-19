import Stage35EntireRelationResidual
import AlgebraicScalarExponential
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! Laurent denominator clearing, global analytic extension, adjoining the
constant coordinate, and finite reindexing. These are proved transports, not
external differential-system hypotheses. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Topology
namespace StrictEUnit

/-- A polynomial over algebraic numbers as a genuine entire function. -/
def stage35_entirePolynomial (p : Polynomial AlgebraicComplex) : entireFunctionAlgebra :=
  Polynomial.eval₂ stage35_entireCoefficient entireCoordinate p

@[simp] theorem stage35_entirePolynomial_apply (p : Polynomial AlgebraicComplex) (z : ℂ) :
    (stage35_entirePolynomial p).val z =
      p.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z := by
  change (entireEvaluation z).toRingHom
    (Polynomial.eval₂ stage35_entireCoefficient entireCoordinate p) = _
  rw [Polynomial.hom_eval₂]
  rfl

/-- The actual polynomial-numerator/common-denominator system on all of C. -/
def Stage35ClearedSystem {ι : Type*} [Fintype ι]
    (f : ι → entireFunctionAlgebra) (t : Polynomial AlgebraicComplex)
    (B : Matrix ι ι (Polynomial AlgebraicComplex)) : Prop :=
  ∀ z i, t.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * deriv (f i).val z =
    ∑ j, (B i j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * (f j).val z

/-- Laurent clearing evaluated only at genuine complex units. -/
theorem stage35_arithmetic_clearing_eval (a : LaurentPolynomial AlgebraicComplex)
    (p : Polynomial AlgebraicComplex) (N : ℕ)
    (hp : Polynomial.toLaurent p = a * LaurentPolynomial.T (N : ℤ)) (z : ℂˣ) :
    p.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom (z : ℂ) =
      (z : ℂ)^N * arithmeticLaurentEvaluation z a := by
  have hh := congrArg (arithmeticLaurentEvaluation z) hp
  simpa only [arithmeticLaurentEvaluation, LaurentPolynomial.eval₂_toLaurent,
    map_mul, LaurentPolynomial.eval₂_T_n, mul_comm] using hh

/-- Every finite Laurent system of actual entire functions has a global
polynomial presentation with denominator X^N, whose value at 1 is exactly 1.
This includes empty index types and proves the equation at the origin. -/
theorem stage35_laurent_exists_global_clearing {ι : Type*} [Fintype ι]
    (f : ι → entireFunctionAlgebra) (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hs : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : Matrix ι ι (Polynomial AlgebraicComplex),
      (∀ i j, Polynomial.toLaurent (B i j) = A i j * LaurentPolynomial.T (N : ℤ)) ∧
      (Polynomial.X ^ N : Polynomial AlgebraicComplex).eval 1 = 1 ∧
      Stage35ClearedSystem f (Polynomial.X ^ N) B := by
  obtain ⟨N, hN, B, hB⟩ := stage16_laurentMatrix_exists_positive_clearing A
  refine ⟨N, hN, B, hB, by simp, ?_⟩
  intro z i
  let r : entireFunctionAlgebra :=
    stage35_entirePolynomial (Polynomial.X ^ N) * entireFunctionDerivative (f i) -
      ∑ j, stage35_entirePolynomial (B i j) * f j
  have hr (w : ℂ) : r.val w = w^N * deriv (f i).val w -
      ∑ j, (B i j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom w * (f j).val w := by
    change (entireEvaluation w).toRingHom r = _
    have hsub (a b : entireFunctionAlgebra) : (entireEvaluation w).toRingHom (a-b) =
        (entireEvaluation w).toRingHom a - (entireEvaluation w).toRingHom b :=
      RingHom.map_sub _ a b
    have hsum (a : ι → entireFunctionAlgebra) : (entireEvaluation w).toRingHom (∑ j, a j) =
        ∑ j, (entireEvaluation w).toRingHom (a j) :=
      map_sum (entireEvaluation w).toRingHom a Finset.univ
    simp only [r, hsub, hsum, RingHom.map_mul]
    change (stage35_entirePolynomial (Polynomial.X ^ N)).val w * deriv (f i).val w -
      ∑ j, (stage35_entirePolynomial (B i j)).val w * (f j).val w = _
    simp only [stage35_entirePolynomial_apply, Polynomial.eval₂_X_pow]
  have hlocal : r.val =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with w hw
    rw [hr]
    have hsys := hs (Units.mk0 w hw) i
    change deriv (f i).val w = _ at hsys
    rw [hsys, Finset.mul_sum]
    apply sub_eq_zero.mpr
    apply Finset.sum_congr rfl
    intro j hj
    have hc := stage35_arithmetic_clearing_eval _ _ _ (hB i j) (Units.mk0 w hw)
    simp only [Units.val_mk0] at hc ⊢
    rw [hc, mul_assoc]
  have hz := stage35_entire_zero_of_local r hlocal z
  rw [hr, sub_eq_zero] at hz
  simpa only [Polynomial.eval₂_X_pow] using hz

/-- Adjoin the genuine constant function 1, with no nonempty-index assumption. -/
def stage35_augmentFunctions {ι : Type*} (f : ι → entireFunctionAlgebra) :
    Option ι → entireFunctionAlgebra := fun o => o.elim 1 f

/-- Zero first row and column extend the system by the constant solution 1. -/
def stage35_augmentMatrix {ι : Type*} (B : Matrix ι ι (Polynomial AlgebraicComplex)) :
    Matrix (Option ι) (Option ι) (Polynomial AlgebraicComplex) :=
  fun i j => match i, j with
    | some i, some j => B i j
    | _, _ => 0

theorem stage35_augmentFunctions_strict {ι : Type*} (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, IsStrictEFunction (f i).val) :
    ∀ i, IsStrictEFunction (stage35_augmentFunctions f i).val := by
  intro i
  cases i with
  | none => simpa [stage35_augmentFunctions] using
      algebraic_constant_isStrictEFunction (1 : AlgebraicComplex)
  | some i => exact hf i

theorem stage35_augment_clearedSystem {ι : Type*} [Fintype ι]
    (f : ι → entireFunctionAlgebra) (t : Polynomial AlgebraicComplex)
    (B : Matrix ι ι (Polynomial AlgebraicComplex)) (hs : Stage35ClearedSystem f t B) :
    Stage35ClearedSystem (stage35_augmentFunctions f) t (stage35_augmentMatrix B) := by
  intro z i
  cases i with
  | none => simp [stage35_augmentFunctions, stage35_augmentMatrix]
  | some i => simpa [stage35_augmentFunctions, stage35_augmentMatrix,
      Fintype.sum_option] using hs z i

/-- Finite reindexing preserves the actual global cleared system. -/
theorem stage35_reindex_clearedSystem {ι τ : Type*} [Fintype ι] [Fintype τ]
    (e : ι ≃ τ) (f : ι → entireFunctionAlgebra) (t : Polynomial AlgebraicComplex)
    (B : Matrix ι ι (Polynomial AlgebraicComplex)) (hs : Stage35ClearedSystem f t B) :
    Stage35ClearedSystem (fun j => f (e.symm j)) t
      (fun i j => B (e.symm i) (e.symm j)) := by
  intro z i
  rw [hs z (e.symm i)]
  exact (e.symm.sum_comp fun j =>
    (B (e.symm i) j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * (f j).val z).symm

end StrictEUnit
