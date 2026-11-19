import LaurentLogBase
import Mathlib.RingTheory.Derivation.Basic

noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]

def v5LaurentEulerLinear : LaurentPolynomial k →ₗ[k] LaurentPolynomial k where
  toFun f := Finsupp.onFinset f.support (fun n => (n : k) * f n)
    (by intro n hn; exact Finsupp.mem_support_iff.mpr (fun hz => hn (by change (n:k)*f n=0; rw [hz, mul_zero])))
  map_add' f g := by ext n; exact mul_add _ _ _
  map_smul' c f := by ext n; change (n:k) * (c * f n) = c * ((n:k)*f n); ring

@[simp] theorem v5LaurentEulerLinear_single (n : ℤ) (c : k) :
    v5LaurentEulerLinear (Finsupp.single n c) = Finsupp.single n ((n:k)*c) := by
  ext j
  by_cases h : n = j
  · subst j; change (n:k) * (Finsupp.single n c) n = (Finsupp.single n ((n:k)*c)) n; simp only [Finsupp.single_eq_same]
  · change (j:k) * (Finsupp.single n c) j = (Finsupp.single n ((n:k)*c)) j; simp only [Finsupp.single_apply, if_neg h, mul_zero]

theorem v5LaurentEulerLinear_mul (f g : LaurentPolynomial k) :
    v5LaurentEulerLinear (f*g) = v5LaurentEulerLinear f * g + f * v5LaurentEulerLinear g := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp only [add_mul, map_add, hf, hg, mul_add]; abel
  | C_mul_T n c =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    induction g using LaurentPolynomial.induction_on' with
    | add f g hf hg => simp only [mul_add, map_add, hf, hg, add_mul]; abel
    | C_mul_T m d =>
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.single_mul_single, v5LaurentEulerLinear_single]
      rw [← Finsupp.single_add]
      congr 1
      push_cast
      ring

def v5LaurentBaseDerivation : Derivation k (LaurentPolynomial k) (LaurentPolynomial k) where
  toFun f := LaurentPolynomial.T (-1) * v5LaurentEulerLinear f
  map_add' f g := by rw [map_add, mul_add]
  map_smul' c f := by rw [map_smul]; exact mul_smul_comm _ _ _
  map_one_eq_zero' := by
    change LaurentPolynomial.T (-1) * v5LaurentEulerLinear ((Finsupp.single (0:ℤ) (1:k) : LaurentPolynomial k)) = 0
    rw [v5LaurentEulerLinear_single]; simp only [Int.cast_zero, zero_mul, Finsupp.single_zero, mul_zero]
  leibniz' f g := by
    change LaurentPolynomial.T (-1) * v5LaurentEulerLinear (f*g) = f * (LaurentPolynomial.T (-1) * v5LaurentEulerLinear g) + g * (LaurentPolynomial.T (-1) * v5LaurentEulerLinear f)
    rw [v5LaurentEulerLinear_mul]
    ring

@[simp] theorem v5LaurentBaseDerivation_single (n : ℤ) (c : k) :
    v5LaurentBaseDerivation (Finsupp.single n c) =
      Finsupp.single (n-1) ((n:k)*c) := by
  change LaurentPolynomial.T (-1) * v5LaurentEulerLinear (Finsupp.single n c) = _
  rw [v5LaurentEulerLinear_single, LaurentPolynomial.single_eq_C_mul_T,
    LaurentPolynomial.single_eq_C_mul_T]
  rw [mul_comm (LaurentPolynomial.T (-1)), mul_assoc, ← LaurentPolynomial.T_add]
  congr 2

@[simp] theorem v5LaurentBaseDerivation_C (c : k) :
    v5LaurentBaseDerivation (LaurentPolynomial.C c) = 0 := by
  change v5LaurentBaseDerivation (Finsupp.single 0 c) = 0
  rw [v5LaurentBaseDerivation_single]; simp only [Int.cast_zero, zero_mul, Finsupp.single_zero]

@[simp] theorem v5LaurentBaseDerivation_T (n : ℤ) :
    v5LaurentBaseDerivation (LaurentPolynomial.T n : LaurentPolynomial k) =
      LaurentPolynomial.C (n:k) * LaurentPolynomial.T (n-1) := by
  change v5LaurentBaseDerivation (Finsupp.single n 1) = _
  rw [v5LaurentBaseDerivation_single, mul_one, LaurentPolynomial.single_eq_C_mul_T]

theorem v5LaurentBaseDerivation_polynomial (p : Polynomial k) :
    v5LaurentBaseDerivation p.toLaurent = p.derivative.toLaurent := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.derivative_add, hp, hq]
  | monomial n c =>
    rw [Polynomial.toLaurent_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      v5LaurentBaseDerivation_single, Polynomial.derivative_monomial, Polynomial.toLaurent_C_mul_T]
    cases n with
    | zero => simp
    | succ n =>
      rw [LaurentPolynomial.single_eq_C_mul_T]
      congr 1
      · congr 1; push_cast; ring
      · congr 1; push_cast; omega

theorem v5LaurentBase_stable_ideal_eq_top [CharZero k]
    (I : Ideal (LaurentPolynomial k))
    (hI : ∀ f ∈ I, v5LaurentBaseDerivation f ∈ I)
    (hne : I ≠ ⊥) : I = ⊤ := by
  have hp : ∀ p : Polynomial k, p ≠ 0 → p.toLaurent ∈ I → I = ⊤ := by
    intro p
    induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
    | h n ih =>
      intro hp0 hpI
      by_cases hd : p.derivative = 0
      · have he := Polynomial.eq_C_of_derivative_eq_zero hd
        have hc : p.coeff 0 ≠ 0 := by
          intro hz
          apply hp0
          rw [he, hz, Polynomial.C_0]
        rw [he, Polynomial.toLaurent_C] at hpI
        apply Ideal.eq_top_of_isUnit_mem I hpI
        exact (isUnit_iff_ne_zero.mpr hc).map LaurentPolynomial.C
      · apply ih p.derivative.natDegree
          (hn ▸ Polynomial.natDegree_derivative_lt (fun hz => hd (by
            rw [Polynomial.eq_C_of_natDegree_eq_zero hz, Polynomial.derivative_C])))
          p.derivative rfl hd
        simpa only [v5LaurentBaseDerivation_polynomial] using hI _ hpI
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, p, he⟩ := LaurentPolynomial.exists_T_pow x
  apply hp p
  · intro hz
    have hxT : x * LaurentPolynomial.T (n : ℤ) = 0 := by rw [← he, hz, map_zero]
    exact hx0 ((LaurentPolynomial.isUnit_T (R := k) (n:ℤ)).mul_right_cancel
      (by simpa using hxT))
  · rw [he]
    exact I.mul_mem_right _ hx


end StrictEUnit
#print axioms StrictEUnit.v5LaurentBaseDerivation
#print axioms StrictEUnit.v5LaurentBaseDerivation_polynomial
#print axioms StrictEUnit.v5LaurentBase_stable_ideal_eq_top
