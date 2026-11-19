import V5ODEDifferential
import V5ODEInverse
import V5LocalLogODE
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
open scoped Matrix.L2OpNorm Topology
open LaurentPolynomial
namespace StrictEUnit

variable {K : Type*} [CommSemiring K]

/-- Track the prefactor from the derivative of the exponential substitution, at every
integer exponent (including negative Laurent exponents). -/
theorem v5_laurent_eval_exp_shift (f : K →+* ℂ) (p : LaurentPolynomial K)
    (J : Finset ℤ) (hJ : p.support ⊆ J) (w : ℂ) :
    Complex.exp w * LaurentPolynomial.eval₂ f (Units.mk0 _ (Complex.exp_ne_zero w)) p =
      ∑ n ∈ J, Complex.exp (((n : ℂ) + 1) * w) * f (p n) := by
  classical
  have hp : (∑ n ∈ J, Finsupp.single n (p n) : LaurentPolynomial K) = p := by
    apply Finsupp.ext
    intro n
    rw [Finsupp.finset_sum_apply]
    by_cases hn : n ∈ J
    · rw [Finset.sum_eq_single n]
      · exact Finsupp.single_eq_same
      · exact fun k _ hk => Finsupp.single_eq_of_ne hk
      · exact fun h => (h hn).elim
    · rw [Finset.sum_eq_zero]
      · symm
        exact Finsupp.not_mem_support_iff.mp (fun h => hn (hJ h))
      · exact fun k hk => Finsupp.single_eq_of_ne (fun e => hn (e ▸ hk))
  conv_lhs => rw [← hp]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [single_eq_C_mul_T, eval₂_C_mul_T, Units.val_zpow_eq_zpow_val, Units.val_mk0,
    ← Complex.exp_int_mul, add_mul, one_mul, Complex.exp_add]
  ring

/-- Entrywise evaluation of the Laurent coefficient matrix on nonzero complex numbers,
with zero at the unused point 0. -/
def v5EvalLaurentMatrix {ι : Type*} (f : K →+* ℂ)
    (A : Matrix ι ι (LaurentPolynomial K)) (z : ℂ) : Matrix ι ι ℂ :=
  if hz : z = 0 then 0 else
    fun i j => LaurentPolynomial.eval₂ f (Units.mk0 z hz) (A i j)

theorem v5_laurent_matrix_exp_shift {ι : Type*} [Fintype ι] (f : K →+* ℂ)
    (A : Matrix ι ι (LaurentPolynomial K)) :
    ∃ (J : Finset ℤ) (B : ℤ → Matrix ι ι ℂ), ∀ w : ℂ,
      Complex.exp w • v5EvalLaurentMatrix f A (Complex.exp w) =
        ∑ n ∈ J, Complex.exp (((n : ℂ) + 1) * w) • B n := by
  classical
  let J := (Finset.univ : Finset (ι × ι)).biUnion (fun ij => (A ij.1 ij.2).support)
  refine ⟨J, fun n i j => f (A i j n), fun w => ?_⟩
  ext i j
  have hJ : (A i j).support ⊆ J := Finset.subset_biUnion_of_mem (fun ij => (A ij.1 ij.2).support)
    (Finset.mem_univ (i, j))
  simpa only [v5EvalLaurentMatrix, dif_neg (Complex.exp_ne_zero w), Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply] using v5_laurent_eval_exp_shift f (A i j) J hJ w

/-- Entire existence for the actual Euler-transformed Laurent-matrix system. -/
theorem v5_laurent_matrix_ode_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : K →+* ℂ) (A : Matrix ι ι (LaurentPolynomial K)) (U0 : Matrix ι ι ℂ) :
    ∃ U : ℂ → Matrix ι ι ℂ, U 0 = U0 ∧ ∀ w : ℂ, HasDerivAt U
      (Complex.exp w • (v5EvalLaurentMatrix f A (Complex.exp w) * U w)) w := by
  obtain ⟨J, B, hB⟩ := v5_laurent_matrix_exp_shift f A
  obtain ⟨U, h0, hU⟩ := v5_finite_exponential_ode_exists J B (fun n => (n : ℂ) + 1) U0
  refine ⟨U, h0, fun w => ?_⟩
  simpa only [← hB w, smul_mul_assoc] using hU w

/-- Undo the exponential change near the actual marked point 1. -/
theorem v5_laurent_matrix_ode_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : K →+* ℂ) (A : Matrix ι ι (LaurentPolynomial K)) (U0 : Matrix ι ι ℂ) :
    ∃ U : ℂ → Matrix ι ι ℂ, Differentiable ℂ U ∧
      U (Complex.log 1) = U0 ∧ ∀ᶠ z in 𝓝 (1 : ℂ),
        HasDerivAt (fun z => U (Complex.log z))
          (v5EvalLaurentMatrix f A z * U (Complex.log z)) z := by
  obtain ⟨U, h0, hU⟩ := v5_laurent_matrix_ode_exists f A U0
  refine ⟨U, fun w => (hU w).differentiableAt, ?_, ?_⟩
  · simpa only [Complex.log_one] using h0
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with z hz
  exact v5_log_pullback_hasDerivAt _ U hU hz

/-- Entire normalized fundamental matrix of a Laurent system on the logarithmic
cover, together with its entire two-sided matrix inverse. -/
theorem v5_laurent_matrix_ode_inverse_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : K →+* ℂ) (A : Matrix ι ι (LaurentPolynomial K)) :
    ∃ U V : ℂ → Matrix ι ι ℂ, U 0 = 1 ∧ V 0 = 1 ∧
      (∀ w, HasDerivAt U
        (Complex.exp w • (v5EvalLaurentMatrix f A (Complex.exp w) * U w)) w) ∧
      Differentiable ℂ V ∧ ∀ w, V w * U w = 1 ∧ U w * V w = 1 := by
  obtain ⟨J, B, hB⟩ := v5_laurent_matrix_exp_shift f A
  obtain ⟨U, V, hU0, hV0, hU, hV, hinv⟩ :=
    v5_finite_exponential_matrix_ode_inverse_exists
      (AlgEquiv.refl : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ) J B (fun n => (n : ℂ) + 1)
  refine ⟨U, V, hU0, hV0, fun w => ?_, fun w => (hV w).differentiableAt, hinv⟩
  simpa only [← hB w, smul_mul_assoc] using hU w

theorem v5_matrix_entry_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : ℂ → Matrix ι ι ℂ} (hU : Differentiable ℂ U) (i j : ι) :
    Differentiable ℂ (fun w => U w i j) := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  change Differentiable ℂ (L ∘ U)
  exact Differentiable.comp (g := L) (f := U) L.differentiable hU

theorem v5_matrix_det_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : ℂ → Matrix ι ι ℂ} (hU : Differentiable ℂ U) :
    Differentiable ℂ (fun w => (U w).det) := by
  simp_rw [Matrix.det_apply']
  apply Differentiable.sum
  intro σ _
  apply (differentiable_const _).mul
  apply Differentiable.finset_prod
  exact fun i _ => v5_matrix_entry_differentiable hU (σ i) i

/-- The actual coefficient matrix has an entire normalized solution on the cover
and a nowhere singular determinant with an entire reciprocal; the logarithmic
pullback solves the original equation near its mark 1. -/
theorem v5_laurent_matrix_ode_marked_entire {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : K →+* ℂ) (A : Matrix ι ι (LaurentPolynomial K)) :
    ∃ (U : ℂ → Matrix ι ι ℂ) (v : ℂ → ℂ),
      U (Complex.log 1) = 1 ∧
      Differentiable ℂ U ∧ Differentiable ℂ v ∧
      (∀ w, v w * (U w).det = 1) ∧
      (∀ᶠ z in 𝓝 (1 : ℂ), HasDerivAt (fun z => U (Complex.log z))
        (v5EvalLaurentMatrix f A z * U (Complex.log z)) z) := by
  obtain ⟨U, V, hU0, _, hU, hV, hinv⟩ := v5_laurent_matrix_ode_inverse_exists f A
  refine ⟨U, fun w => (V w).det, ?_, fun w => (hU w).differentiableAt,
    v5_matrix_det_differentiable hV, ?_, ?_⟩
  · simpa only [Complex.log_one] using hU0
  · intro w
    rw [← Matrix.det_mul, (hinv w).1, Matrix.det_one]
  · filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with z hz
    exact v5_log_pullback_hasDerivAt _ U hU hz

end StrictEUnit
#print axioms StrictEUnit.v5_laurent_eval_exp_shift
#print axioms StrictEUnit.v5_laurent_matrix_exp_shift
#print axioms StrictEUnit.v5_laurent_matrix_ode_exists
#print axioms StrictEUnit.v5_laurent_matrix_ode_local
#print axioms StrictEUnit.v5_laurent_matrix_ode_inverse_exists
#print axioms StrictEUnit.v5_matrix_entry_differentiable
#print axioms StrictEUnit.v5_matrix_det_differentiable
#print axioms StrictEUnit.v5_laurent_matrix_ode_marked_entire
