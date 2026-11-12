import PolynomialConnectionClearing

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

section Algebra
variable {B : Type*} [CommRing B]

theorem clearedConnection_sum_step {r : ℕ}
    (t dt n : B) (C dC v dv : Fin r → B)
    (U : Matrix (Fin r) (Fin r) B)
    (hv : ∀ j : Fin r, t * dv j = ∑ l, U j l * v l) :
    t * (∑ j, (dC j * v j + C j * dv j)) - n * dt * (∑ j, C j * v j) =
      ∑ j, (t * dC j - n * dt * C j + ∑ l, C l * U l j) * v j := by
  classical
  have hc : (∑ j, (∑ l, C l * U l j) * v j) =
      ∑ l, C l * (t * dv l) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hc]
  have h1 : t * (∑ j, dC j * v j) = ∑ j, t * dC j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h2 : n * dt * (∑ j, C j * v j) = ∑ j, n * dt * C j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h3 : t * (∑ j, C j * dv j) = ∑ j, C j * (t * dv j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [mul_add, h1, h2, h3]
  ring

end Algebra

section Derivation
variable {k K B : Type*} [Field k] [Field K] [CommRing B] [Algebra k B]

theorem clearedConnection_mul_derivation_pow (d : Derivation k B B) (t : B) (n : ℕ) :
    t * d (t^n) = (n : B) * t^n * d t := by
  cases n with
  | zero => simp
  | succ n =>
    rw [d.leibniz_pow]
    simp only [Nat.succ_sub_one, nsmul_eq_mul, smul_eq_mul, pow_succ]
    ring

/-- Literal higher derivative identity for the SAME cleared polynomial
connection. It uses the RIGHT-product recurrence without any inverse. -/
theorem polynomialConnectionSequence_cleared_solution
    (d : Derivation k B B) (φ : Polynomial K →+* B)
    (hderiv : ∀ p : Polynomial K, d (φ p) = φ p.derivative)
    {r : ℕ} (T : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (v : Fin r → B)
    (hv : ∀ i, φ T * d (v i) = ∑ j, φ (U i j) * v j) :
    ∀ n i, (φ T)^n * (d^[n] (v i)) =
      ∑ j, φ (polynomialConnectionSequence T U n i j) * v j := by
  classical
  intro n
  induction n with
  | zero =>
    intro i
    simp only [polynomialConnectionSequence, Matrix.one_apply,
      pow_zero, one_mul, Function.iterate_zero_apply]
    simp
  | succ n ih =>
    intro i
    have hp := clearedConnection_mul_derivation_pow d (φ T) n
    calc
      (φ T)^(n+1) * d^[n+1] (v i) =
          φ T * d ((φ T)^n * d^[n] (v i)) -
            (n:B) * d (φ T) * ((φ T)^n * d^[n] (v i)) := by
        rw [Function.iterate_succ_apply', d.leibniz]
        simp only [smul_eq_mul]
        symm
        calc
          _ = (φ T)^(n+1) * d (d^[n] (v i)) +
              (φ T * d ((φ T)^n) - (n:B)*(φ T)^n*d (φ T)) * d^[n] (v i) := by
                rw [pow_succ]
                ring
          _ = _ := by rw [hp, sub_self, zero_mul, add_zero]
      _ = φ T * d (∑ j, φ (polynomialConnectionSequence T U n i j) * v j) -
          (n:B) * d (φ T) * (∑ j, φ (polynomialConnectionSequence T U n i j) * v j) := by
        rw [ih i]
      _ = ∑ j, (φ T * d (φ (polynomialConnectionSequence T U n i j)) -
          (n:B) * d (φ T) * φ (polynomialConnectionSequence T U n i j) +
          ∑ l, φ (polynomialConnectionSequence T U n i l) * φ (U l j)) * v j := by
        have hd : d (∑ j, φ (polynomialConnectionSequence T U n i j) * v j) =
            ∑ j, (d (φ (polynomialConnectionSequence T U n i j)) * v j +
              φ (polynomialConnectionSequence T U n i j) * d (v j)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [d.leibniz]
          simp only [smul_eq_mul]
          ring
        rw [hd]
        exact clearedConnection_sum_step (φ T) (d (φ T)) (n:B)
          (fun j => φ (polynomialConnectionSequence T U n i j))
          (fun j => d (φ (polynomialConnectionSequence T U n i j)))
          v (fun j => d (v j)) (fun j l => φ (U j l)) hv
      _ = ∑ j, φ (polynomialConnectionSequence T U (n+1) i j) * v j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [polynomialConnectionSequence, map_add, map_sub, map_mul,
          map_natCast, map_sum, hderiv]

end Derivation
end StrictEUnit
end
