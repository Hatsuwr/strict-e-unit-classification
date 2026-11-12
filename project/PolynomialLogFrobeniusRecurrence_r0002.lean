import PolynomialDifferentialOperator
import PolynomialResonanceBudget
import FiniteLogLaurentTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Init

/-!
# A constructed polynomial-log Frobenius coefficient recurrence

Let B(k,T) be the coefficient of z^k in a scalar Euler differential operator.
For sum_i b_i(z) theta^i this is B(k,T) = sum_i b_i(k) T^i. Its indicial
polynomial is P(T)=B(0,T), assumed nonzero when proving the equation.

After removing the formal exponent z^rho, the coefficient equation is the
literal convolution sum_{s=0}^n B(n-s,D_L+rho+s) u_s = 0. In particular the
lower terms use rho+s, NOT rho+n. A well-founded recursion solves the diagonal
P(D_L+rho+n) by the checked polynomial right inverse, allowing every resonance.
Any initial polynomial in ker P(D_L+rho) is retained exactly.

The checked finite resonance budget bounds every log degree by
natDegree(u_0)+natDegree(P). The checked transpose then produces the amplitude
in Polynomial (LaurentSeries K), retaining all natural-exponent/log-degree
coefficients. The exponent z^rho is NOT asserted to lie in that ring.

This constructs one formal coefficient solution for prescribed initial data.
It does not claim a full basis, independence, convergence, rational exponents,
arithmetic bounds, ramification compatibility, or the Stage43 source equation.
SOURCE-ONLY DRAFT: no compiler was run by this worker.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Shifted constant-coefficient operators do not raise log degree. -/
theorem shiftedPolynomialDifferentialOperator_natDegree_le
    (c : K) (P f : Polynomial K) :
    (shiftedPolynomialDifferentialOperator c P f).natDegree ≤ f.natDegree := by
  rw [shiftedPolynomialDifferentialOperator_eq]
  exact polynomialDifferentialOperator_natDegree_le _ _

/-- Coefficient symbols of the concrete scalar Euler operator
`sum_{i=0}^r b_i(z) theta^i`, where `b i k` is the z^k coefficient of b_i. -/
def scalarEulerCoefficientSymbol (r : ℕ) (b : Fin (r + 1) → ℕ → K)
    (k : ℕ) : Polynomial K :=
  ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (b i k)

/-- The symbol acts by precisely the indicated shifted Euler iterates. -/
theorem scalarEulerCoefficientSymbol_apply (r : ℕ)
    (b : Fin (r + 1) → ℕ → K) (k : ℕ) (c : K) (f : Polynomial K) :
    shiftedPolynomialDifferentialOperator c (scalarEulerCoefficientSymbol r b k) f =
      ∑ i : Fin (r + 1), b i k • (shiftedPolynomialDerivative c)^[i.val] f := by
  simp only [shiftedPolynomialDifferentialOperator, scalarEulerCoefficientSymbol,
    map_sum, Polynomial.aeval_monomial, LinearMap.sum_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_apply]

/-- Strictly lower convolution. The argument needs only coefficients s<n. -/
def polynomialLogLowerSum (B : ℕ → Polynomial K) (rho : K) (n : ℕ)
    (v : Fin n → Polynomial K) : Polynomial K :=
  ∑ s : Fin n,
    shiftedPolynomialDifferentialOperator (rho + (s.val : K)) (B (n - s.val)) (v s)

/-- The exact nth coefficient of the scalar Euler equation after removing z^rho. -/
def polynomialLogEulerCoefficient (B : ℕ → Polynomial K) (rho : K)
    (u : ℕ → Polynomial K) (n : ℕ) : Polynomial K :=
  ∑ s : Fin (n + 1),
    shiftedPolynomialDifferentialOperator (rho + (s.val : K)) (B (n - s.val)) (u s.val)

/-- For actual scalar Euler symbols the equation is the full two-index
convolution, including all lower shifts rho+s. -/
theorem polynomialLogEulerCoefficient_scalar_formula (r : ℕ)
    (b : Fin (r + 1) → ℕ → K) (rho : K) (u : ℕ → Polynomial K) (n : ℕ) :
    polynomialLogEulerCoefficient (scalarEulerCoefficientSymbol r b) rho u n =
      ∑ s : Fin (n + 1), ∑ i : Fin (r + 1),
        b i (n - s.val) • (shiftedPolynomialDerivative (rho + (s.val : K)))^[i.val]
          (u s.val) := by
  unfold polynomialLogEulerCoefficient
  apply Finset.sum_congr rfl
  intro s _
  exact scalarEulerCoefficientSymbol_apply _ _ _ _ _

/-- The last convolution summand is exactly the shifted indicial operator. -/
theorem polynomialLogEulerCoefficient_split (B : ℕ → Polynomial K) (rho : K)
    (u : ℕ → Polynomial K) (n : ℕ) :
    polynomialLogEulerCoefficient B rho u n =
      polynomialLogLowerSum B rho n (fun s => u s.val) +
        shiftedPolynomialDifferentialOperator (rho + (n : K)) (B 0) (u n) := by
  rw [polynomialLogEulerCoefficient, Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, Nat.sub_self, polynomialLogLowerSum]

/-- Uniformly bounded lower data give a lower forcing term with the same bound. -/
theorem polynomialLogLowerSum_natDegree_le (B : ℕ → Polynomial K) (rho : K)
    (n : ℕ) (v : Fin n → Polynomial K) (d : ℕ)
    (hv : ∀ s, (v s).natDegree ≤ d) :
    (polynomialLogLowerSum B rho n v).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s _
  exact (shiftedPolynomialDifferentialOperator_natDegree_le _ _ _).trans (hv s)

/-- In particular the forcing degree is bounded by the largest preceding degree.
For n=0 both the empty sum and its natural degree are zero. -/
theorem polynomialLogLowerSum_natDegree_le_sup (B : ℕ → Polynomial K) (rho : K)
    (u : ℕ → Polynomial K) (n : ℕ) :
    (polynomialLogLowerSum B rho n (fun s => u s.val)).natDegree ≤
      (Finset.range n).sup (fun s => (u s).natDegree) := by
  apply polynomialLogLowerSum_natDegree_le
  intro s
  exact Finset.le_sup (f := fun s => (u s).natDegree)
    (Finset.mem_range.mpr s.isLt)

section CharZero
variable [CharZero K]

/-- Genuine well-founded construction from the strictly earlier coefficients.
At positive indices choose the explicit particular solution; no kernel correction
is inserted. The initial coefficient is prescribed and never inverted. -/
def polynomialLogFrobeniusCoefficient (B : ℕ → Polynomial K) (rho : K)
    (u0 : Polynomial K) (n : ℕ) : Polynomial K :=
  Nat.strongRecOn' (P := fun _ => Polynomial K) n fun m lower =>
    if m = 0 then u0 else
      shiftedPolynomialDifferentialRightInverse (rho + (m : K)) (B 0)
        (-polynomialLogLowerSum B rho m (fun s => lower s.val s.isLt))

/-- Exact unfolding equation for the well-founded recurrence. -/
theorem polynomialLogFrobeniusCoefficient_eq (B : ℕ → Polynomial K) (rho : K)
    (u0 : Polynomial K) (n : ℕ) :
    polynomialLogFrobeniusCoefficient B rho u0 n =
      if n = 0 then u0 else
        shiftedPolynomialDifferentialRightInverse (rho + (n : K)) (B 0)
          (-polynomialLogLowerSum B rho n
            (fun s => polynomialLogFrobeniusCoefficient B rho u0 s.val)) := by
  unfold polynomialLogFrobeniusCoefficient
  rw [Nat.strongRecOn'_beta]

@[simp] theorem polynomialLogFrobeniusCoefficient_zero (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) :
    polynomialLogFrobeniusCoefficient B rho u0 0 = u0 := by
  rw [polynomialLogFrobeniusCoefficient_eq, if_pos rfl]

/-- Each positive coefficient solves its actual forced indicial equation. -/
theorem polynomialLogFrobeniusCoefficient_recurrence (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) (hP : B 0 ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    shiftedPolynomialDifferentialOperator (rho + (n : K)) (B 0)
        (polynomialLogFrobeniusCoefficient B rho u0 n) =
      -polynomialLogLowerSum B rho n
        (fun s => polynomialLogFrobeniusCoefficient B rho u0 s.val) := by
  rw [polynomialLogFrobeniusCoefficient_eq, if_neg hn]
  exact shiftedPolynomialDifferentialRightInverse_apply _ _ _ hP

/-- All coefficient equations vanish, including the initial kernel equation. -/
theorem polynomialLogFrobeniusCoefficient_equation (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) (hP : B 0 ≠ 0)
    (hu0 : shiftedPolynomialDifferentialOperator rho (B 0) u0 = 0) (n : ℕ) :
    polynomialLogEulerCoefficient B rho
      (polynomialLogFrobeniusCoefficient B rho u0) n = 0 := by
  rw [polynomialLogEulerCoefficient_split]
  by_cases hn : n = 0
  · subst n
    simpa [polynomialLogLowerSum] using hu0
  · rw [polynomialLogFrobeniusCoefficient_recurrence B rho u0 hP n hn,
      add_neg_cancel]

/-- The constructed recurrence supplies the lower-triangular degree inequality;
it is not an existence or growth assumption on an unspecified solution. -/
theorem polynomialLogFrobeniusCoefficient_degree_step (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) (n : ℕ) :
    (polynomialLogFrobeniusCoefficient B rho u0 n).natDegree ≤
      max u0.natDegree
        ((Finset.range n).sup (fun s =>
          (polynomialLogFrobeniusCoefficient B rho u0 s).natDegree)) +
      polynomialResonanceMultiplicity rho (B 0) n := by
  by_cases hn : n = 0
  · subst n
    rw [polynomialLogFrobeniusCoefficient_zero]
    exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  · have hforcing :
        (-polynomialLogLowerSum B rho n
          (fun s => polynomialLogFrobeniusCoefficient B rho u0 s.val)).natDegree ≤
        max u0.natDegree
          ((Finset.range n).sup (fun s =>
            (polynomialLogFrobeniusCoefficient B rho u0 s).natDegree)) := by
      rw [Polynomial.natDegree_neg]
      exact (polynomialLogLowerSum_natDegree_le_sup B rho _ n).trans (le_max_right _ _)
    rw [polynomialLogFrobeniusCoefficient_eq, if_neg hn]
    exact (shiftedPolynomialDifferentialRightInverse_natDegree_le _ _ _).trans
      (Nat.add_le_add_right hforcing _)

/-- A single finite logarithmic-degree bound, with no global nonresonance premise. -/
theorem polynomialLogFrobeniusCoefficient_uniform_degree (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) (n : ℕ) :
    (polynomialLogFrobeniusCoefficient B rho u0 n).natDegree ≤
      u0.natDegree + (B 0).natDegree :=
  polynomialResonance_uniform_degree_bound rho (B 0)
    (fun s => (polynomialLogFrobeniusCoefficient B rho u0 s).natDegree) u0.natDegree
    (polynomialLogFrobeniusCoefficient_degree_step B rho u0) n

/-- Vanishing above one global log-degree cutoff, in the exact transpose API. -/
theorem polynomialLogFrobeniusCoefficient_coeff_eq_zero (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) (n j : ℕ)
    (hj : u0.natDegree + (B 0).natDegree + 1 ≤ j) :
    (polynomialLogFrobeniusCoefficient B rho u0 n).coeff j = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact (polynomialLogFrobeniusCoefficient_uniform_degree B rho u0 n).trans_lt
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hj)

/-- The bounded-log Frobenius amplitude, without adjoining the exponent z^rho. -/
def polynomialLogFrobeniusAmplitude (B : ℕ → Polynomial K) (rho : K)
    (u0 : Polynomial K) : Polynomial (LaurentSeries K) :=
  finiteLogLaurentTranspose (u0.natDegree + (B 0).natDegree + 1)
    ((PowerSeries.mk (polynomialLogFrobeniusCoefficient B rho u0) :
      PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K))

/-- Every coefficient survives the exact finite-log transpose. -/
theorem polynomialLogFrobeniusAmplitude_coeff (B : ℕ → Polynomial K) (rho : K)
    (u0 : Polynomial K) (j n : ℕ) :
    ((polynomialLogFrobeniusAmplitude B rho u0).coeff j).coeff (n : ℤ) =
      (polynomialLogFrobeniusCoefficient B rho u0 n).coeff j :=
  finiteLogLaurentTranspose_powerSeries_mk_coeff _ _
    (polynomialLogFrobeniusCoefficient_coeff_eq_zero B rho u0) j n

/-- A nonzero prescribed seed gives a nonzero coefficient solution. -/
theorem polynomialLogFrobeniusCoefficient_ne_zero (B : ℕ → Polynomial K)
    (rho : K) (u0 : Polynomial K) (hu0 : u0 ≠ 0) :
    polynomialLogFrobeniusCoefficient B rho u0 ≠ (fun _ => 0) := by
  intro hz
  apply hu0
  simpa only [polynomialLogFrobeniusCoefficient_zero] using congrFun hz 0

/-- Distinct prescribed seeds remain distinct at coefficient zero. -/
theorem polynomialLogFrobeniusCoefficient_seed_injective (B : ℕ → Polynomial K)
    (rho : K) : Function.Injective (polynomialLogFrobeniusCoefficient B rho) := by
  intro u0 v0 h
  simpa only [polynomialLogFrobeniusCoefficient_zero] using congrFun h 0

/-- The constant seed is available at every root of the nonzero indicial
polynomial, including roots of multiplicity greater than one. -/
theorem shiftedPolynomialDifferentialOperator_one_eq_zero_of_root
    (rho : K) (P : Polynomial K) (hP : P ≠ 0) (hroot : P.eval rho = 0) :
    shiftedPolynomialDifferentialOperator rho P 1 = 0 := by
  apply (shiftedPolynomialDifferentialOperator_kernel_iff rho P 1 hP).mpr
  rw [Polynomial.degree_one]
  exact WithBot.coe_lt_coe.mpr ((Polynomial.rootMultiplicity_pos hP).mpr hroot)

/-- Exact existence package: prescribed initial data, the scalar coefficient
ODE, one uniform degree bound, and an actual finite-log Laurent amplitude. -/
theorem exists_polynomialLogFrobeniusSolution (B : ℕ → Polynomial K) (rho : K)
    (u0 : Polynomial K) (hP : B 0 ≠ 0)
    (hu0 : shiftedPolynomialDifferentialOperator rho (B 0) u0 = 0) :
    ∃ u : ℕ → Polynomial K,
      u 0 = u0 ∧
      (∀ n, polynomialLogEulerCoefficient B rho u n = 0) ∧
      (∀ n, (u n).natDegree ≤ u0.natDegree + (B 0).natDegree) ∧
      ∃ p : Polynomial (LaurentSeries K),
        ∀ j n : ℕ, (p.coeff j).coeff (n : ℤ) = (u n).coeff j := by
  refine ⟨polynomialLogFrobeniusCoefficient B rho u0,
    polynomialLogFrobeniusCoefficient_zero B rho u0,
    polynomialLogFrobeniusCoefficient_equation B rho u0 hP hu0,
    polynomialLogFrobeniusCoefficient_uniform_degree B rho u0,
    polynomialLogFrobeniusAmplitude B rho u0, ?_⟩
  exact polynomialLogFrobeniusAmplitude_coeff B rho u0

end CharZero
end StrictEUnit

#print axioms StrictEUnit.polynomialLogFrobeniusCoefficient
#print axioms StrictEUnit.polynomialLogFrobeniusCoefficient_recurrence
#print axioms StrictEUnit.polynomialLogFrobeniusCoefficient_equation
#print axioms StrictEUnit.polynomialLogFrobeniusCoefficient_uniform_degree
#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_coeff
#print axioms StrictEUnit.exists_polynomialLogFrobeniusSolution
