import TensorLinearization
import HomogeneousLiftingReconstruction

/-!
New reconstruction of the missing tensor-word interface, not recovered source.
The tensor tuple is the full family of actual products.  Its connection uses
exactly the supplied clearing polynomial, and the span identity recovers the
supplied homogeneous polynomial itself, with no scalar normalization.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Topology
namespace StrictEUnit

/-- Actual products indexed by all words of length `D`. -/
def liftingTensorPowerFunctions {ι : Type*}
    (f : ι → entireFunctionAlgebra) (D : ℕ) :
    (Fin D → ι) → entireFunctionAlgebra := tensorWordFunctions f

/-- The full tensor connection, with all single-letter transitions retained. -/
def liftingTensorPowerMatrix {ι : Type*} [Fintype ι]
    (B : Matrix ι ι (Polynomial AlgebraicComplex)) (D : ℕ) :
    Matrix (Fin D → ι) (Fin D → ι) (Polynomial AlgebraicComplex) :=
  tensorWordMatrix B

theorem liftingTensorPowerFunctions_strict {ι : Type*}
    (f : ι → entireFunctionAlgebra) (hf : ∀ i, IsStrictEFunction (f i).val)
    (D : ℕ) : ∀ w, IsStrictEFunction (liftingTensorPowerFunctions f D w).val :=
  fun w => tensorWordFunctions_strict f hf w

theorem liftingTensorPower_clearedSystem {ι : Type*} [Fintype ι]
    (f : ι → entireFunctionAlgebra) (t : Polynomial AlgebraicComplex)
    (B : Matrix ι ι (Polynomial AlgebraicComplex))
    (hs : Stage35ClearedSystem f t B) (D : ℕ) :
    Stage35ClearedSystem (liftingTensorPowerFunctions f D) t
      (liftingTensorPowerMatrix B D) :=
  tensorWordFunctions_clearedSystem f t B hs

/-- A word gives the product of the corresponding original variables. -/
def liftingTensorWordForm {ι R : Type*} [CommSemiring R]
    (D : ℕ) (w : Fin D → ι) : MvPolynomial ι R :=
  tensorWordMonomial D w

theorem liftingTensorWordForm_homogeneous {ι R : Type*} [CommSemiring R]
    (D : ℕ) (w : Fin D → ι) :
    (liftingTensorWordForm (R := R) D w).IsHomogeneous D :=
  tensorWordMonomial_homogeneous D w

/-- Evaluation is the actual product function, at every complex point. -/
theorem liftingTensorWordForm_eval {ι : Type*}
    (f : ι → entireFunctionAlgebra) (D : ℕ) (w : Fin D → ι) (z : ℂ) :
    MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
      (fun i => (f i).val z) (liftingTensorWordForm (R := AlgebraicComplex) D w) =
      (liftingTensorPowerFunctions f D w).val z := by
  simp [liftingTensorWordForm, tensorWordMonomial, liftingTensorPowerFunctions,
    tensorWordFunctions_apply]

/-- Aggregate coefficients onto chosen words representing each supported
exponent vector.  Repeated words are permitted; all words remain in the family.
The result is a literal identity, including for the zero polynomial and degree
zero, and requires no division or nonzero coefficient hypothesis. -/
theorem homogeneous_eq_sum_tensorWords {ι R : Type*} [Fintype ι] [CommSemiring R]
    (D : ℕ) (P : MvPolynomial ι R) (hP : P.IsHomogeneous D) :
    ∃ p : (Fin D → ι) → R,
      P = ∑ w, MvPolynomial.C (p w) * liftingTensorWordForm D w := by
  classical
  have hdegree : ∀ d ∈ P.support, d.degree = D := by
    intro d hd
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero hne)
  have hwords : ∀ d : P.support,
      ∃ w : Fin D → ι, liftingTensorWordForm (R := R) D w =
        MvPolynomial.monomial d.val 1 := by
    intro d
    exact exists_tensorWordMonomial D d.val (hdegree d.val d.property)
  choose w hw using hwords
  let p : (Fin D → ι) → R :=
    fun u => ∑ d : P.support, if w d = u then P.coeff d.val else 0
  have hsupport : P = ∑ d : P.support,
      MvPolynomial.C (P.coeff d.val) * liftingTensorWordForm D (w d) := by
    simp only [hw, MvPolynomial.C_mul_monomial, mul_one]
    exact ((Finset.sum_coe_sort P.support
      (fun d => MvPolynomial.monomial d (P.coeff d))).trans
        (MvPolynomial.support_sum_monomial_coeff P)).symm
  refine ⟨p, hsupport.trans ?_⟩
  symm
  calc
    (∑ u, MvPolynomial.C (p u) * liftingTensorWordForm D u) =
        ∑ u, ∑ d : P.support,
          if w d = u then
            MvPolynomial.C (P.coeff d.val) * liftingTensorWordForm D u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [p, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : w d = u <;>
        simp only [h, if_true, if_false, map_zero, zero_mul]
    _ = ∑ d : P.support, ∑ u,
          if w d = u then
            MvPolynomial.C (P.coeff d.val) * liftingTensorWordForm D u else 0 :=
      Finset.sum_comm
    _ = ∑ d : P.support,
          MvPolynomial.C (P.coeff d.val) * liftingTensorWordForm D (w d) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Fintype.sum_ite_eq (w d)
        (fun u => MvPolynomial.C (P.coeff d.val) * liftingTensorWordForm D u)

end StrictEUnit
