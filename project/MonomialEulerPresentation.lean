import EulerFallingConnectionArithmetic
import FiniteForcingArithmeticClosure

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The exact Euler matrix after weighting coordinate i by z^(w i). -/
def monomialEulerConnection {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ) :
    Matrix (Fin r) (Fin r) (LaurentSeries K) := fun i j =>
  (w i : LaurentSeries K)*(1 : Matrix (Fin r) (Fin r) (LaurentSeries K)) i j+
    laurentIntegerMonomial ((w i : ℤ)+1-(w j : ℤ))*A i j

/-- Normalized and ordinary gauge matrices are identified literally. -/
theorem monomialEulerConnection_gauge {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ) :
    diagonalGaugeConnection (stage14_laurentAlgebraDerivation (k:=K)) A
      (fun i =>laurentIntegerMonomial (w i : ℤ))=
      fun i j =>laurentIntegerMonomial (-1)*monomialEulerConnection A w i j := by
  funext i j
  apply mul_left_cancel₀ (laurentIntegerMonomial_ne_zero (K:=K) 1)
  apply mul_right_cancel₀ (laurentIntegerMonomial_ne_zero (K:=K) (w j : ℤ))
  change laurentIntegerMonomial 1*((stage14_laurentAlgebraDerivation
      (laurentIntegerMonomial (w i : ℤ))*(1 : Matrix (Fin r) (Fin r) (LaurentSeries K)) i j+
      laurentIntegerMonomial (w i : ℤ)*A i j)/laurentIntegerMonomial (w j : ℤ))*laurentIntegerMonomial (w j : ℤ)=_
  rw [mul_assoc,div_mul_cancel₀ _ (laurentIntegerMonomial_ne_zero _),mul_add]
  have hd : laurentIntegerMonomial (K:=K) 1*stage14_laurentAlgebraDerivation
      (laurentIntegerMonomial (w i : ℤ))=(w i : LaurentSeries K)*laurentIntegerMonomial (w i : ℤ) := by
    change laurentIntegerMonomial 1*laurentOrdinaryDerivation (laurentIntegerMonomial (w i : ℤ))=_
    rw [← laurentEuler_eq_coordinate_mul_ordinary,laurentEuler_nat_monomial]
  rw [← mul_assoc,hd]
  have he : laurentIntegerMonomial (K:=K) 1*laurentIntegerMonomial (-1)=1 := by simp
  rw [← mul_assoc (laurentIntegerMonomial 1) (laurentIntegerMonomial (-1)),he,one_mul]
  simp only [monomialEulerConnection,add_mul]
  have hdiag : (w i : LaurentSeries K)*laurentIntegerMonomial (w i : ℤ)*
      (1 : Matrix (Fin r) (Fin r) (LaurentSeries K)) i j=
      ((w i : LaurentSeries K)*(1 : Matrix (Fin r) (Fin r) (LaurentSeries K)) i j)*laurentIntegerMonomial (w j : ℤ) := by
    by_cases hij : i=j
    · subst j;ring
    · simp [Matrix.one_apply,hij]
  rw [hdiag]
  congr 1
  calc
    _=(laurentIntegerMonomial (K:=K) 1*laurentIntegerMonomial (w i : ℤ))*A i j := by ring
    _=(laurentIntegerMonomial ((w i : ℤ)+1-(w j : ℤ))*laurentIntegerMonomial (w j : ℤ))*A i j := by
      rw [laurentIntegerMonomial_mul,laurentIntegerMonomial_mul];congr 2;omega
    _=_ := by ring

/-- A common natural weight shift adds exactly a scalar diagonal to the Euler
matrix. Nonnegative weights suffice even when the original forcing has poles. -/
theorem monomialEulerConnection_weight_shift {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ) (a : ℕ) :
    monomialEulerConnection A (fun i =>a+w i)=
      monomialEulerConnection A w+Matrix.diagonal (fun _ =>(a : LaurentSeries K)) := by
  funext i j
  simp only [monomialEulerConnection,Matrix.add_apply,Matrix.diagonal_apply,Nat.cast_add]
  have he : (a : ℤ)+(w i : ℤ)+1-((a : ℤ)+(w j : ℤ))=(w i : ℤ)+1-(w j : ℤ) := by omega
  rw [he]
  by_cases hij : i=j
  · subst j;simp only [Matrix.one_apply,ite_true,mul_one];ring
  · simp [Matrix.one_apply,hij]

/-- The genuine existing Laurent divided-connection arithmetic transfers to
any exactly identified regular Euler presentation via the PROVED monomial
formula. No arithmetic of the new matrix is assumed. -/
theorem monomialEulerPresentation_divided_arithmetic [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hreal : monomialEulerConnection A w=C.map (HahnSeries.ofPowerSeries ℤ K))
    (hA : LaurentDividedConnectionArithmetic A) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)) := by
  obtain ⟨P,B,hB,hpole,hden⟩ := hA
  let W := ∑ i,w i
  have hw : ∀ i,w i≤W := fun i =>Finset.single_le_sum (fun i _ =>Nat.zero_le (w i)) (Finset.mem_univ i)
  obtain ⟨hE,hD⟩ := laurent_diagonal_gauge_exponential_denominators A w W hw B hB (by
    intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden N
    exact ⟨D,hD,hDb,fun m hm l hl i j =>hDi m hm i j l hl⟩)
  refine ⟨B^(W+3),hE,powerSeriesEulerDividedConnection_denominators C _ ?_⟩
  have hg : diagonalGaugeConnection (stage14_laurentAlgebraDerivation (k:=K)) A
      (fun i =>laurentIntegerMonomial (w i : ℤ))=powerSeriesEulerOrdinaryMatrix C := by
    rw [monomialEulerConnection_gauge,hreal]
    rfl
  rw [hg] at hD
  exact hD

end StrictEUnit
end
