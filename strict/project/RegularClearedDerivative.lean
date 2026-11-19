import WeightedCompanionSupport

noncomputable section
namespace StrictEUnit

/-- Strictly below the regular (including equal-slope) face the SAME
cleared differential numerator still vanishes. On the face it need not. -/
theorem polynomial_expand_derivative_below_regular_face
    {R : Type*} [CommRing R] (T P : Polynomial R) (c : R)
    (h t e a k : ℕ) (hh : 0<h)
    (hT : ∀ i,i<t → T.coeff i=0)
    (hP : ∀ i,i<e → (Polynomial.expand R h P).coeff i=0)
    (hha : h≤a) (ha : a≤h*t) (hk : k<e+(h*t-a)) :
    (Polynomial.expand R h (T*P.derivative-Polynomial.C c*T.derivative*P)).coeff k=0 := by
  rw [Polynomial.coeff_expand hh]
  split_ifs with hd
  · apply weighted_cleared_derivative_coeff_eq_zero T P c h t e (k/h) hT
    · intro i hi
      rw [← Polynomial.coeff_expand_mul' hh P i]
      exact hP (h*i) hi
    · rw [Nat.mul_div_cancel' hd]
      omega
  · rfl

/-- Boundary coefficient of a derivative product. The e=0 case is proved
separately, so natural subtraction cannot manufacture a negative coefficient. -/
theorem polynomial_coeff_mul_derivative_at_lower_bounds
    {R : Type*} [CommRing R] (T P : Polynomial R) (t e : ℕ) (ht : 0<t)
    (hT : ∀ i,i<t → T.coeff i=0) (hP : ∀ i,i<e → P.coeff i=0) :
    (T*P.derivative).coeff (e+t-1)=T.coeff t*(P.coeff e*(e:R)) := by
  cases e with
  | zero =>
    have hz := polynomial_coeff_mul_eq_zero_of_shifted_lower_bounds T P.derivative
      t 0 0 (0+t-1) (by simpa using hT) (by intro j hj;omega) (by omega)
    simpa only [Nat.zero_add,Nat.cast_zero,mul_zero] using hz
  | succ e =>
    have hD : ∀ i,i<e → P.derivative.coeff i=0 := by
      intro i hi
      rw [Polynomial.coeff_derivative,hP (i+1) (by omega),zero_mul]
    have hx := polynomial_coeff_mul_at_lower_bounds T P.derivative t e hT hD
    have hi : e+1+t-1=t+e := by omega
    rw [hi,hx,Polynomial.coeff_derivative]
    simp only [Nat.cast_add,Nat.cast_one]

theorem polynomial_coeff_derivative_mul_at_lower_bounds
    {R : Type*} [CommRing R] (T P : Polynomial R) (t e : ℕ) (ht : 0<t)
    (hT : ∀ i,i<t → T.coeff i=0) (hP : ∀ i,i<e → P.coeff i=0) :
    (T.derivative*P).coeff (e+t-1)=(T.coeff t*(t:R))*P.coeff e := by
  have hD : ∀ i,i<t-1 → T.derivative.coeff i=0 := by
    intro i hi
    rw [Polynomial.coeff_derivative,hT (i+1) (by omega),zero_mul]
  have hx := polynomial_coeff_mul_at_lower_bounds T.derivative P (t-1) e hD hP
  have hi : e+t-1=(t-1)+e := by omega
  rw [hi,hx,Polynomial.coeff_derivative,show t-1+1=t by omega]
  have hc : (((t-1:ℕ):R)+1)=(t:R) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun k : ℕ => (k:R)) (show t-1+1=t by omega)
  rw [hc]

/-- The exact regular boundary retains the derivative contribution. -/
theorem polynomial_cleared_derivative_regular_boundary
    {R : Type*} [CommRing R] (T P : Polynomial R) (c : R) (t e : ℕ) (ht : 0<t)
    (hT : ∀ i,i<t → T.coeff i=0) (hP : ∀ i,i<e → P.coeff i=0) :
    (T*P.derivative-Polynomial.C c*T.derivative*P).coeff (e+t-1)=
      ((e:R)-c*(t:R))*T.coeff t*P.coeff e := by
  rw [Polynomial.coeff_sub,mul_assoc (Polynomial.C c),Polynomial.coeff_C_mul,
    polynomial_coeff_mul_derivative_at_lower_bounds T P t e ht hT hP,
    polynomial_coeff_derivative_mul_at_lower_bounds T P t e ht hT hP]
  ring

end StrictEUnit
end
