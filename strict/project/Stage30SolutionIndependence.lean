import DifferentialConstantsIndependence
import FormalAmbientDifferentialField
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independence of solutions of one differential system over its exact
constant field implies independence over the ambient field. The conclusion
is proved by normalized finite-support relations, not assumed as a frame
or Wronskian hypothesis. This does not construct an arithmetic solution basis. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k E ι n : Type*} [Field k] [Field E] [Algebra k E]

/-- Differentiating a zero relation between solutions of one system cancels
the common matrix term and leaves a relation between derivative coefficients. -/
theorem stage30_solution_relation_derivative [Fintype n]
    (d : Derivation k E E) (A : Matrix n n E) (v : ι → n → E)
    (hv : ∀ j i, d (v j i) = ∑ l, A i l * v j l)
    (s : Finset ι) (f : ι → E) (hf : ∑ j ∈ s, f j • v j = 0) :
    ∑ j ∈ s, d (f j) • v j = 0 := by
  classical
  funext i
  have hcoord : ∀ l, ∑ j ∈ s, f j * v j l = 0 := by
    intro l
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrFun hf l
  have hder := congrArg d (hcoord i)
  simp only [map_sum, d.leibniz, hv, smul_eq_mul, map_zero] at hder
  have hcancel : ∑ j ∈ s, f j * (∑ l, A i l * v j l) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      ∑ l, ∑ j ∈ s, f j * (A i l * v j l) =
          ∑ l, A i l * (∑ j ∈ s, f j * v j l) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by simp only [hcoord, mul_zero, Finset.sum_const_zero]
  simp only [Finset.sum_add_distrib, hcancel, zero_add] at hder
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm]
    using hder

/-- No finiteness assumption is needed for the family of
columns. The system row index is finite. Exact constants convert a
normalized minimal dependence into a dependence over k. -/
theorem stage30_solution_columns_linearIndependent [Fintype n]
    (d : Derivation k E E)
    (hconstants : ∀ a : E, d a = 0 → ∃ c : k, algebraMap k E c = a)
    (A : Matrix n n E) (v : ι → n → E)
    (hv : ∀ j i, d (v j i) = ∑ l, A i l * v j l)
    (hli : LinearIndependent k v) : LinearIndependent E v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro f hf
    have hfa : f a = 0 := by
      by_contra hfa
      let g : ι → E := fun i => (f a)⁻¹ * f i
      have hga : g a = 1 := inv_mul_cancel₀ hfa
      have hg : ∑ i ∈ insert a s, g i • v i = 0 := by
        calc
          ∑ i ∈ insert a s, g i • v i = (f a)⁻¹ • (∑ i ∈ insert a s, f i • v i) := by
            simp only [Finset.smul_sum, smul_smul, g]
          _ = 0 := by rw [hf, smul_zero]
      have hDga : d (g a) = 0 := by rw [hga, d.map_one_eq_zero]
      have hdrel := stage30_solution_relation_derivative d A v hv (insert a s) g hg
      rw [Finset.sum_insert ha, hDga, zero_smul, zero_add] at hdrel
      have hDg : ∀ i ∈ insert a s, d (g i) = 0 := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hDga
        · exact ih (fun j => d (g j)) hdrel i hi
      have hex : ∀ i : ι, ∃ c : k, i ∈ insert a s → algebraMap k E c = g i := by
        intro i
        by_cases hi : i ∈ insert a s
        · obtain ⟨c, hc⟩ := hconstants (g i) (hDg i hi)
          exact ⟨c, fun _ => hc⟩
        · exact ⟨0, fun h => False.elim (hi h)⟩
      choose b hb using hex
      have hkrel : ∑ i ∈ insert a s, b i • v i = 0 := by
        calc
          ∑ i ∈ insert a s, b i • v i = ∑ i ∈ insert a s, g i • v i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hb i hi, IsScalarTower.algebraMap_smul]
          _ = 0 := hg
      have hba : b a = 0 := (linearIndependent_iff'.mp hli) _ b hkrel a
        (Finset.mem_insert_self _ _)
      have hzero : g a = 0 := by
        rw [← hb a (Finset.mem_insert_self _ _), hba, map_zero]
      exact one_ne_zero (hga.symm.trans hzero)
    rw [Finset.sum_insert ha, hfa, zero_smul, zero_add] at hf
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfa
    · exact ih f hf i hi

/-- For a square family the determinant is consequently nonzero. Neither
ambient independence nor determinant nonvanishing is a hypothesis. -/
theorem stage30_solution_matrix_det_ne_zero [Fintype n] [DecidableEq n]
    (d : Derivation k E E)
    (hconstants : ∀ a : E, d a = 0 → ∃ c : k, algebraMap k E c = a)
    (A Y : Matrix n n E)
    (hY : ∀ j i, d (Y i j) = ∑ l, A i l * Y l j)
    (hli : LinearIndependent k (fun j => Yᵀ j)) : Y.det ≠ 0 := by
  have hE : LinearIndependent E (fun j => Yᵀ j) :=
    stage30_solution_columns_linearIndependent d hconstants A _ hY hli
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det Y).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hE))

/-- The formal Laurent/logarithmic ambient field has the required constants
by an existing proved theorem, so this specialization has no constants premise. -/
theorem stage30_formal_solution_matrix_det_ne_zero [CharZero k]
    [Fintype n] [DecidableEq n] (N : ℕ) (hN : N ≠ 0)
    (A Y : Matrix n n (RatFunc (LaurentSeries k)))
    (hY : ∀ j i, formalAmbientDerivation (k := k) N hN (Y i j) = ∑ l, A i l * Y l j)
    (hli : LinearIndependent k (fun j => Yᵀ j)) : Y.det ≠ 0 :=
  stage30_solution_matrix_det_ne_zero (formalAmbientDerivation (k := k) N hN)
    (fun a => (formalAmbientDerivation_constants N hN a).mp) A Y hY hli

/-- Multiplying a derivation by a nonzero field element does not change its
constant field. This is the algebraic transport needed before using ordinary
z-derivatives instead of a scaled Euler derivative. -/
theorem stage30_scaled_derivation_constants (d : Derivation k E E)
    (hc : ∀ x : E, d x = 0 ↔ ∃ c : k, algebraMap k E c = x)
    (u : E) (hu : u ≠ 0) (x : E) :
    (u • d) x = 0 ↔ ∃ c : k, algebraMap k E c = x := by
  change u * d x = 0 ↔ _
  rw [mul_eq_zero, or_iff_right hu, hc]

/-- Exact constants of every nonzero scalar multiple of the actual formal
ambient derivation. Identifying a particular scalar with a transported
ordinary derivative is a separate differential-compatibility assertion. -/
theorem stage30_scaled_formal_constants [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (u : RatFunc (LaurentSeries k)) (hu : u ≠ 0)
    (x : RatFunc (LaurentSeries k)) :
    (u • formalAmbientDerivation (k := k) N hN) x = 0 ↔
      ∃ c : k, algebraMap k (RatFunc (LaurentSeries k)) c = x :=
  stage30_scaled_derivation_constants (formalAmbientDerivation (k := k) N hN)
    (formalAmbientDerivation_constants N hN) u hu x

/-- Solution-column independence for a nonzero rescaling of the actual
formal derivative, still from constants-field independence alone. -/
theorem stage30_scaled_formal_columns_linearIndependent [CharZero k]
    [Fintype n] (N : ℕ) (hN : N ≠ 0)
    (u : RatFunc (LaurentSeries k)) (hu : u ≠ 0)
    (A : Matrix n n (RatFunc (LaurentSeries k)))
    (v : ι → n → RatFunc (LaurentSeries k))
    (hv : ∀ j i, (u • formalAmbientDerivation (k := k) N hN) (v j i) = ∑ l, A i l * v j l)
    (hli : LinearIndependent k v) : LinearIndependent (RatFunc (LaurentSeries k)) v :=
  stage30_solution_columns_linearIndependent (u • formalAmbientDerivation (k := k) N hN)
    (fun x => (stage30_scaled_formal_constants N hN u hu x).mp) A v hv hli

/-- A square solution matrix for the nonzero rescaled formal derivative has
nonzero determinant once its columns are independent over the constants. -/
theorem stage30_scaled_formal_matrix_det_ne_zero [CharZero k]
    [Fintype n] [DecidableEq n] (N : ℕ) (hN : N ≠ 0)
    (u : RatFunc (LaurentSeries k)) (hu : u ≠ 0)
    (A Y : Matrix n n (RatFunc (LaurentSeries k)))
    (hY : ∀ j i, (u • formalAmbientDerivation (k := k) N hN) (Y i j) = ∑ l, A i l * Y l j)
    (hli : LinearIndependent k (fun j => Yᵀ j)) : Y.det ≠ 0 :=
  stage30_solution_matrix_det_ne_zero (u • formalAmbientDerivation (k := k) N hN)
    (fun x => (stage30_scaled_formal_constants N hN u hu x).mp) A Y hY hli

end StrictEUnit
