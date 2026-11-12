import LaurentLogBasePoint
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The exact kernel of the actual manuscript basepoint t=1, ell=0.
This proves the presentation ideal; no fiber-kernel premise is supplied. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
variable (k : Type*) [Field k]

def laurentLogBaseT : (LaurentLogBase k)ˣ where
  val := Polynomial.C (LaurentPolynomial.T 1)
  inv := Polynomial.C (LaurentPolynomial.T (-1))
  val_inv := by rw [← map_mul, ← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← map_mul, ← LaurentPolynomial.T_add]; simp

def laurentLogBasePointIdeal : Ideal (LaurentLogBase k) :=
  Ideal.span {((laurentLogBaseT k : (LaurentLogBase k)ˣ) : LaurentLogBase k)-1, Polynomial.X}

@[simp] theorem laurentEvaluateOne_T (n : ℤ) :
    laurentEvaluateOne k (LaurentPolynomial.T n) = 1 :=
  laurentEvaluateOne_single k n 1

@[simp] theorem laurentEvaluateOne_C (a : k) :
    laurentEvaluateOne k (LaurentPolynomial.C a) = a :=
  laurentEvaluateOne_single k 0 a

theorem laurentLogBasePoint_surjective : Function.Surjective (laurentLogBasePoint k) := by
  intro a
  exact ⟨algebraMap k (LaurentLogBase k) a, (laurentLogBasePoint k).commutes a⟩

theorem laurentLogBasePointIdeal_le_ker :
    laurentLogBasePointIdeal k ≤ RingHom.ker (laurentLogBasePoint k).toRingHom := by
  apply Ideal.span_le.mpr
  intro r hr
  rcases hr with rfl | hr
  · change laurentLogBasePoint k (Polynomial.C (LaurentPolynomial.T 1)-1) = 0
    simp
  · have he : r = Polynomial.X := Set.mem_singleton_iff.mp hr
    subst r
    exact laurentLogBasePoint_X k

theorem laurentLogBasePoint_quotient_normal_form (p : LaurentLogBase k) :
    Ideal.Quotient.mk (laurentLogBasePointIdeal k) p =
      Ideal.Quotient.mk (laurentLogBasePointIdeal k)
        (algebraMap k (LaurentLogBase k) (laurentLogBasePoint k p)) := by
  let J := laurentLogBasePointIdeal k
  letI : CommRing (LaurentLogBase k ⧸ J) := Ideal.Quotient.commRing J
  let q : Polynomial (LaurentPolynomial k) →+*
      (Polynomial (LaurentPolynomial k) ⧸ J) := Ideal.Quotient.mk J
  have ht : q (Polynomial.C (LaurentPolynomial.T 1)) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one q, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp [J,laurentLogBasePointIdeal,laurentLogBaseT])
  have hti : q (Polynomial.C (LaurentPolynomial.T (-1))) = 1 := by
    have h := congrArg q (laurentLogBaseT k).val_inv
    change q (Polynomial.C (LaurentPolynomial.T 1) *
      Polynomial.C (LaurentPolynomial.T (-1))) = q 1 at h
    simp only [map_mul, map_one, ht] at h
    exact (one_mul _).symm.trans h
  have htn (n : ℤ) : q (Polynomial.C (LaurentPolynomial.T n)) = 1 := by
    induction n using Int.induction_on with
    | hz => simp [q]
    | hp n ih =>
      rw [LaurentPolynomial.T_add, map_mul, map_mul, ih, ht]
      exact one_mul (1 : LaurentLogBase k ⧸ J)
    | hn n ih =>
      rw [sub_eq_add_neg, LaurentPolynomial.T_add, map_mul, map_mul, ih, hti]
      exact one_mul (1 : LaurentLogBase k ⧸ J)
  have hl : q Polynomial.X = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp [J,laurentLogBasePointIdeal])
  have hc (f : LaurentPolynomial k) : q (Polynomial.C f) =
      q (algebraMap k (LaurentLogBase k) (laurentEvaluateOne k f)) := by
    induction f using LaurentPolynomial.induction_on' with
    | add f g hf hg => simp only [map_add, hf, hg]
    | C_mul_T n a =>
      rw [map_mul, map_mul, htn]
      rw [mul_one (q (Polynomial.C (LaurentPolynomial.C a))), map_mul,
        laurentEvaluateOne_C, laurentEvaluateOne_T, mul_one]
      rfl
  change q p = q (algebraMap k (LaurentLogBase k) (laurentLogBasePoint k p))
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, hp, hr]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, hl]
    cases n with
    | zero => simpa using hc a
    | succ n =>
      change q (Polynomial.C a) * (0 : Polynomial (LaurentPolynomial k) ⧸ J) ^ (n+1) = _
      rw [zero_pow (Nat.succ_ne_zero n), mul_zero]
      simp

theorem laurentLogBasePoint_kernel :
    RingHom.ker (laurentLogBasePoint k).toRingHom = laurentLogBasePointIdeal k := by
  apply le_antisymm _ (laurentLogBasePointIdeal_le_ker k)
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [laurentLogBasePoint_quotient_normal_form]
  change laurentLogBasePoint k p = 0 at hp
  rw [hp, map_zero, map_zero]

def laurentLogBasePointQuotientEquiv :
    (LaurentLogBase k ⧸ laurentLogBasePointIdeal k) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (laurentLogBasePoint_kernel k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (laurentLogBasePoint_surjective k))

@[simp] theorem laurentLogBasePointQuotientEquiv_mk (p : LaurentLogBase k) :
    laurentLogBasePointQuotientEquiv k (Ideal.Quotient.mk (laurentLogBasePointIdeal k) p) =
      laurentLogBasePoint k p := by
  simp [laurentLogBasePointQuotientEquiv]
  rfl

end StrictEUnit
#print axioms StrictEUnit.laurentLogBaseT
#print axioms StrictEUnit.laurentLogBasePointIdeal
#print axioms StrictEUnit.laurentEvaluateOne_T
#print axioms StrictEUnit.laurentEvaluateOne_C
#print axioms StrictEUnit.laurentLogBasePoint_surjective
#print axioms StrictEUnit.laurentLogBasePointIdeal_le_ker
#print axioms StrictEUnit.laurentLogBasePoint_quotient_normal_form
#print axioms StrictEUnit.laurentLogBasePoint_kernel
#print axioms StrictEUnit.laurentLogBasePointQuotientEquiv
#print axioms StrictEUnit.laurentLogBasePointQuotientEquiv_mk
