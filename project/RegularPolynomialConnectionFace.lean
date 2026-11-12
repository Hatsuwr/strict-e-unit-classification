import RegularWeightedCompanionSupport
import PolynomialConnectionFaceRecurrence

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

theorem polynomialConnectionFaceRow_one {K : Type*} [Field K] (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (m : ℕ) (j : Fin (n+1)) :
    polynomialConnectionFaceRow n 1 1 T U m j=
      (polynomialConnectionSequence T U m 0 j).coeff
        (m*(T.natTrailingDegree-1)+j.val) := by
  simp only [polynomialConnectionFaceRow,irregularPolynomialWeight,
    Polynomial.expand_one,Nat.one_mul,Nat.mul_one]

/-- The actual regular slope-one face of the SAME polynomial sequence.
Its derivative term is retained; no recurrence or support is supplied. -/
theorem polynomialConnectionFaceRow_regular_recurrence
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (ht : 0<T.natTrailingDegree)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1)) :
    polynomialConnectionFaceRow n 1 1 T U 0=(Pi.single 0 1 : Fin (n+1) → K) ∧
    ∀ m,
      polynomialConnectionFaceRow n 1 1 T U (m+1) 0=
        T.coeff T.natTrailingDegree*((0:K)-(m:K))*polynomialConnectionFaceRow n 1 1 T U m 0+
        polynomialConnectionFaceRow n 1 1 T U m (Fin.last n)*polynomialCompanionFace n 1 1 T U 0 ∧
      ∀ j : Fin n,polynomialConnectionFaceRow n 1 1 T U (m+1) j.succ=
        T.coeff T.natTrailingDegree*((j.succ.val:K)-(m:K))*
          polynomialConnectionFaceRow n 1 1 T U m j.succ+
        (polynomialConnectionFaceRow n 1 1 T U m j.castSucc*T.coeff T.natTrailingDegree+
          polynomialConnectionFaceRow n 1 1 T U m (Fin.last n)*
            polynomialCompanionFace n 1 1 T U j.succ) := by
  classical
  let s := T.natTrailingDegree
  let e (m j : ℕ) := m*(s-1)+j
  have hs : 1≤s := ht
  have hsupport : ∀ m (j : Fin (n+1)) k,k<e m j.val →
      (polynomialConnectionSequence T U m 0 j).coeff k=0 := by
    have hx := polynomialConnectionSequence_expanded_regular_support n c T U hclear
      1 1 Nat.one_pos le_rfl (by simpa using hs)
      (fun j hj => by have hb:=hV j hj;have hji:=j.isLt;simp only [Nat.one_mul,Nat.mul_one];omega)
    simpa only [Polynomial.expand_one,irregularPolynomialWeight,Nat.one_mul,Nat.mul_one] using hx
  have hTlow : ∀ k,k<s → T.coeff k=0 :=
    fun k hk => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk
  have hVlow : ∀ (j : Fin (n+1)) k,k+(n+1-j.val)<s → (U (Fin.last n) j).coeff k=0 := by
    intro j k hk
    by_cases hj : U (Fin.last n) j=0
    · rw [hj,Polynomial.coeff_zero]
    · have hb:=hV j hj
      have hji:=j.isLt
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  constructor
  · funext j
    by_cases hj : j=0
    · subst j
      simp [polynomialConnectionFaceRow_one,polynomialConnectionSequence,Matrix.one_apply,Pi.single_apply]
    · simp [polynomialConnectionFaceRow_one,polynomialConnectionSequence,Matrix.one_apply,
        Pi.single_apply,hj,Ne.symm hj]
  · intro m
    have hd (j : Fin (n+1)) :
        (T*(polynomialConnectionSequence T U m 0 j).derivative-
          (m:Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 j).coeff (e (m+1) j.val)=
        T.coeff s*((j.val:K)-(m:K))*polynomialConnectionFaceRow n 1 1 T U m j := by
      have hi : e (m+1) j.val=e m j.val+s-1 := by
        dsimp [e]
        rw [Nat.add_mul,Nat.one_mul]
        omega
      rw [hi]
      have hx := polynomial_cleared_derivative_regular_boundary T
        (polynomialConnectionSequence T U m 0 j) (m:K) s (e m j.val) ht hTlow (hsupport m j)
      rw [Polynomial.C_eq_natCast] at hx
      rw [hx,polynomialConnectionFaceRow_one]
      change (((e m j.val:ℕ):K)-(m:K)*(s:K))*T.coeff s*
          (polynomialConnectionSequence T U m 0 j).coeff (e m j.val)=_
      dsimp only [e]
      rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hs,Nat.cast_one]
      ring
    have hf (j : Fin (n+1)) :
        (polynomialConnectionSequence T U m 0 (Fin.last n)*U (Fin.last n) j).coeff (e (m+1) j.val)=
        polynomialConnectionFaceRow n 1 1 T U m (Fin.last n)*polynomialCompanionFace n 1 1 T U j := by
      have hi : e (m+1) j.val+(n+1-j.val)=s+e m n := by
        have hji:=j.isLt
        dsimp [e]
        rw [Nat.add_mul,Nat.one_mul]
        omega
      rw [mul_comm]
      have hx := polynomial_coeff_mul_at_shifted_lower_bound (U (Fin.last n) j)
        (polynomialConnectionSequence T U m 0 (Fin.last n)) s (n+1-j.val) (e m n)
        (e (m+1) j.val) (hVlow j) (hsupport m (Fin.last n)) hi
      rw [hx,polynomialConnectionFaceRow_one]
      simp only [polynomialCompanionFace,Polynomial.expand_one,Nat.one_mul,Nat.mul_one]
      exact mul_comm _ _
    have hshift (j : Fin n) :
        (polynomialConnectionSequence T U m 0 j.castSucc*T).coeff (e (m+1) j.succ.val)=
        polynomialConnectionFaceRow n 1 1 T U m j.castSucc*T.coeff s := by
      have hi : e (m+1) j.succ.val=e m j.val+s := by
        dsimp [e]
        simp only [Fin.val_succ,Nat.add_mul,Nat.one_mul]
        omega
      rw [hi,polynomialConnectionFaceRow_one]
      exact polynomial_coeff_mul_at_lower_bounds _ _ (e m j.val) s
        (by simpa only [Fin.coe_castSucc] using hsupport m j.castSucc) hTlow
    have hrow := polynomialConnectionSequence_companion_first_row n c T U hclear m
    constructor
    · rw [polynomialConnectionFaceRow_one,hrow.1,Polynomial.coeff_add]
      simpa only [e,s,Fin.val_zero,Nat.cast_zero] using congrArg₂ (·+·) (hd 0) (hf 0)
    · intro j
      rw [polynomialConnectionFaceRow_one,hrow.2 j,Polynomial.coeff_add,Polynomial.coeff_add]
      exact congrArg₂ (·+·) (hd j.succ) (congrArg₂ (·+·) (hshift j) (hf j.succ))

end StrictEUnit
end
