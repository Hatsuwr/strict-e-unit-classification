import LaurentLogBase
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Actual coefficient transposition between k[ell][t,t^-1] and k[t,t^-1][ell]. -/
open Polynomial
noncomputable section
namespace StrictEUnit
variable (k : Type*) [CommRing k]

/-- Transpose the two finite coefficient indices. -/
def laurentPolynomialSwapLinear :
    LaurentPolynomial (Polynomial k) ≃ₗ[k] Polynomial (LaurentPolynomial k) :=
  (Finsupp.mapRange.linearEquiv (Polynomial.toFinsuppIsoLinear k)).trans
    ((Finsupp.finsuppProdLEquiv k).symm.trans
      ((Finsupp.domLCongr (R := k) (Equiv.prodComm ℤ ℕ)).trans
        ((Finsupp.finsuppProdLEquiv k).trans
          ((Polynomial.toFinsuppIsoLinear (LaurentPolynomial k)).symm.restrictScalars k))))

@[simp] theorem laurentPolynomialSwapLinear_coeff
    (f : LaurentPolynomial (Polynomial k)) (j : ℕ) (n : ℤ) :
    ((laurentPolynomialSwapLinear k f).coeff j) n = (f n).coeff j := by
  change ((Finsupp.finsuppProdLEquiv k)
    (Finsupp.equivMapDomain (Equiv.prodComm ℤ ℕ)
      ((Finsupp.finsuppProdLEquiv k).symm
        ((Finsupp.mapRange.linearEquiv (Polynomial.toFinsuppIsoLinear k)) f)))) j n = _
  simp only [Finsupp.finsuppProdLEquiv_apply, Finsupp.equivMapDomain_apply,
    Finsupp.finsuppProdLEquiv_symm_apply]
  rfl

@[simp] theorem laurentPolynomialSwapLinear_single_monomial
    (n : ℤ) (j : ℕ) (a : k) :
    laurentPolynomialSwapLinear k (Finsupp.single n (Polynomial.monomial j a)) =
      Polynomial.monomial (R := LaurentPolynomial k) j (AddMonoidAlgebra.single n a) := by
  ext j' n'
  rw [laurentPolynomialSwapLinear_coeff]
  by_cases hn : n = n' <;> by_cases hj : j = j' <;>
    simp only [Finsupp.single_apply, Polynomial.coeff_monomial, hn, hj,
      if_true, if_false, Polynomial.coeff_zero, Finsupp.zero_apply]

/-- Transposing the finite coefficients respects both polynomial and Laurent
convolution multiplication. -/
theorem laurentPolynomialSwapLinear_mul
    (f g : LaurentPolynomial (Polynomial k)) :
    laurentPolynomialSwapLinear k (f * g) =
      laurentPolynomialSwapLinear k f * laurentPolynomialSwapLinear k g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [add_mul, map_add, hf, hh]
  | single n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [Finsupp.single_add, add_mul, map_add, hp, hq]
    | monomial i a =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g h hg hh => simp only [mul_add, map_add, hg, hh]
      | single m q =>
        induction q using Polynomial.induction_on' with
        | add q r hq hr => simp only [Finsupp.single_add, mul_add, map_add, hq, hr]
        | monomial j b =>
          simp only [AddMonoidAlgebra.single_mul_single, Polynomial.monomial_mul_monomial,
            laurentPolynomialSwapLinear_single_monomial]

theorem laurentPolynomialSwapLinear_one :
    laurentPolynomialSwapLinear k 1 = 1 := by
  simpa only [Polynomial.monomial_zero_left, map_one, ← AddMonoidAlgebra.one_def] using
    laurentPolynomialSwapLinear_single_monomial k 0 0 1

/-- The actual coefficient-swap algebra equivalence, not an assumed
identification of the two polynomial presentations of the PV base. -/
def laurentPolynomialSwap :
    LaurentPolynomial (Polynomial k) ≃ₐ[k] Polynomial (LaurentPolynomial k) :=
  AlgEquiv.ofLinearEquiv (laurentPolynomialSwapLinear k)
    (laurentPolynomialSwapLinear_one k) (laurentPolynomialSwapLinear_mul k)

@[simp] theorem laurentPolynomialSwap_coeff
    (f : LaurentPolynomial (Polynomial k)) (j : ℕ) (n : ℤ) :
    ((laurentPolynomialSwap k f).coeff j) n = (f n).coeff j :=
  laurentPolynomialSwapLinear_coeff k f j n

end StrictEUnit
#print axioms StrictEUnit.laurentPolynomialSwapLinear
#print axioms StrictEUnit.laurentPolynomialSwapLinear_coeff

#print axioms StrictEUnit.laurentPolynomialSwapLinear_single_monomial
#print axioms StrictEUnit.laurentPolynomialSwapLinear_mul
#print axioms StrictEUnit.laurentPolynomialSwapLinear_one
#print axioms StrictEUnit.laurentPolynomialSwap
#print axioms StrictEUnit.laurentPolynomialSwap_coeff
