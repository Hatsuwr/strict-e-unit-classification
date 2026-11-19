import SameCompanionEulerGaugeConnection

/-! Full power-series Euler falling connections at a regular singular point.
Their arithmetic will come from the original divided connection, not from a
coefficient recurrence with an assumed cancellation property. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

def powerSeriesEulerFallingConnection {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : ℕ → Matrix (Fin r) (Fin r) (PowerSeries K)
  | 0 => 1
  | m+1 => fun i j => powerSeriesEuler (powerSeriesEulerFallingConnection C m i j)+
      ∑ l,powerSeriesEulerFallingConnection C m i l*C l j-
        (m : PowerSeries K)*powerSeriesEulerFallingConnection C m i j

def powerSeriesEulerDividedConnection {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) :
    Matrix (Fin r) (Fin r) (PowerSeries K) :=
  fun i j => PowerSeries.C K ((m.factorial : K)⁻¹)*powerSeriesEulerFallingConnection C m i j

def powerSeriesEulerOrdinaryMatrix {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : Matrix (Fin r) (Fin r) (LaurentSeries K) :=
  fun i j => laurentIntegerMonomial (-1)*HahnSeries.ofPowerSeries ℤ K (C i j)

theorem powerSeriesEuler_laurent (f : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (powerSeriesEuler f)=
      laurentEuler (HahnSeries.ofPowerSeries ℤ K f) := by
  change HahnSeries.ofPowerSeries ℤ K (PowerSeries.X*PowerSeries.derivative K f)=_
  rw [map_mul,← laurentOrdinaryDerivation_ofPowerSeries,laurentEuler_eq_coordinate_mul_ordinary]
  congr 1
  simpa only [pow_one] using (HahnSeries.ofPowerSeries_X_pow (R:=K) (1 : ℕ))

/-- Removing exactly m poles gives the full Euler falling matrix. -/
theorem powerSeriesEulerFallingConnection_laurent {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i j : Fin r) :
    HahnSeries.ofPowerSeries ℤ K (powerSeriesEulerFallingConnection C m i j)=
      laurentIntegerMonomial (m : ℤ)*matrixConnectionSequence
        (stage14_laurentAlgebraDerivation (k:=K)) (powerSeriesEulerOrdinaryMatrix C) m i j := by
  classical
  let A := powerSeriesEulerOrdinaryMatrix C
  have hz (i j : Fin r) : HahnSeries.ofPowerSeries ℤ K (C i j)=laurentIntegerMonomial 1*A i j := by
    change _=laurentIntegerMonomial 1*(laurentIntegerMonomial (-1)*_)
    rw [← mul_assoc,laurentIntegerMonomial_mul]
    simp
  induction m generalizing i j with
  | zero =>
    simp only [powerSeriesEulerFallingConnection,matrixConnectionSequence,Nat.cast_zero,
      laurentIntegerMonomial_zero,one_mul,Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    change HahnSeries.ofPowerSeries ℤ K (powerSeriesEuler (powerSeriesEulerFallingConnection C m i j)+
      ∑ l,powerSeriesEulerFallingConnection C m i l*C l j-
        (m : PowerSeries K)*powerSeriesEulerFallingConnection C m i j)=_
    simp only [map_sub,map_add,map_sum,map_mul,map_natCast,powerSeriesEuler_laurent,ih]
    rw [laurentEuler_integer_shear_step]
    have hsum : (∑ l,laurentIntegerMonomial (m : ℤ)*matrixConnectionSequence
        stage14_laurentAlgebraDerivation A m i l*HahnSeries.ofPowerSeries ℤ K (C l j))=
        laurentIntegerMonomial ((m+1 : ℕ) : ℤ)*
          ∑ l,matrixConnectionSequence stage14_laurentAlgebraDerivation A m i l*A l j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [hz]
      calc
        _ = (laurentIntegerMonomial (m : ℤ)*laurentIntegerMonomial 1)*
          (matrixConnectionSequence stage14_laurentAlgebraDerivation A m i l*A l j) := by ring
        _ = _ := by rw [laurentIntegerMonomial_mul]; simp only [Nat.cast_add,Nat.cast_one]
    change (m : LaurentSeries K)*(laurentIntegerMonomial (m : ℤ)*matrixConnectionSequence
      stage14_laurentAlgebraDerivation A m i j)+laurentIntegerMonomial ((m+1 : ℕ) : ℤ)*
      laurentOrdinaryDerivation (matrixConnectionSequence stage14_laurentAlgebraDerivation A m i j)+
      (∑ l,laurentIntegerMonomial (m : ℤ)*matrixConnectionSequence stage14_laurentAlgebraDerivation A m i l*
        HahnSeries.ofPowerSeries ℤ K (C l j))-
      (m : LaurentSeries K)*(laurentIntegerMonomial (m : ℤ)*matrixConnectionSequence stage14_laurentAlgebraDerivation A m i j)=_
    rw [hsum]
    change _=laurentIntegerMonomial ((m+1 : ℕ) : ℤ)*
      (laurentOrdinaryDerivation (matrixConnectionSequence stage14_laurentAlgebraDerivation A m i j)+
        ∑ l,matrixConnectionSequence stage14_laurentAlgebraDerivation A m i l*A l j)
    ring

theorem powerSeriesEulerDividedConnection_laurent {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i j : Fin r) :
    HahnSeries.ofPowerSeries ℤ K (powerSeriesEulerDividedConnection C m i j)=
      laurentIntegerMonomial (m : ℤ)*(matrixConnectionSequence
        (stage14_laurentAlgebraDerivation (k:=K)) (powerSeriesEulerOrdinaryMatrix C) m i j/
          (m.factorial : LaurentSeries K)) := by
  unfold powerSeriesEulerDividedConnection
  rw [map_mul,powerSeriesEulerFallingConnection_laurent]
  have hc : HahnSeries.ofPowerSeries ℤ K (PowerSeries.C K ((m.factorial : K)⁻¹))=
      (m.factorial : LaurentSeries K)⁻¹ := by
    rw [HahnSeries.ofPowerSeries_C,map_inv₀, map_natCast]
  rw [hc]
  ring

/-- Operator arithmetic after pole removal: one denominator covers ALL entries,
derivative orders and coefficient degrees in a rectangular prefix. -/
theorem powerSeriesEulerDividedConnection_denominators {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (E : ℝ)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N → ∀ l : ℤ,l≤(N : ℤ) → ∀ i j,
        IsIntegral ℤ ((D : K)*(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K))
          (powerSeriesEulerOrdinaryMatrix C) m i j/(m.factorial : LaurentSeries K)).coeff l)) :
    ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N → ∀ l,l≤N → ∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)) := by
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm l hl i j
  have h := congrArg (fun f : LaurentSeries K => f.coeff (l : ℤ))
    (powerSeriesEulerDividedConnection_laurent C m i j)
  dsimp only at h
  rw [HahnSeries.ofPowerSeries_apply_coeff] at h
  have hx : (l : ℤ)=((l : ℤ)-(m : ℤ))+(m : ℤ) := by omega
  conv_rhs at h => arg 2; rw [hx]
  rw [laurentIntegerMonomial,HahnSeries.coeff_single_mul_add,one_mul] at h
  rw [h]
  apply hDi m hm
  exact le_trans (sub_le_self _ (Int.natCast_nonneg m)) (by exact_mod_cast hl)

end StrictEUnit
end
