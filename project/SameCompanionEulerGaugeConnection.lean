import RationalLaurentConnectionTransport

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The original cleared companion really maps to its rational inclusion. -/
theorem same_companion_laurent_clearing
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (i j : Fin (n+1)) :
    polynomialLaurentImage (U i j)=polynomialLaurentImage T*
      algebraMap (RatFunc K) (LaurentSeries K) (minimalDerivativeCompanion (n+1) c i j) := by
  have h := congrArg (algebraMap (RatFunc K) (LaurentSeries K)) (hclear i j)
  simpa only [map_mul,← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K),
    Polynomial.algebraMap_hahnSeries_apply,polynomialLaurentImage] using h

/-- Entrywise identity with the PREVIOUSLY constructed regular Euler matrix.
No differential-system equivalence is substituted for the actual matrix equality. -/
theorem same_companion_euler_gauge_matrix
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1)) :
    diagonalGaugeConnection (stage14_laurentAlgebraDerivation (k:=K))
      (fun i j => algebraMap (RatFunc K) (LaurentSeries K) (minimalDerivativeCompanion (n+1) c i j))
      (fun i => laurentIntegerMonomial (i.val : ℤ))=
        fun i j => laurentIntegerMonomial (-1)*sameCompanionLaurentEulerMatrix n T U i j := by
  classical
  let A : Matrix (Fin (n+1)) (Fin (n+1)) (LaurentSeries K) := fun i j =>
    algebraMap (RatFunc K) (LaurentSeries K) (minimalDerivativeCompanion (n+1) c i j)
  let s : Fin (n+1) → LaurentSeries K := fun i => laurentIntegerMonomial (i.val : ℤ)
  have hder (i : Fin (n+1)) : laurentIntegerMonomial 1*
      stage14_laurentAlgebraDerivation (s i)=(i.val : LaurentSeries K)*s i := by
    change laurentIntegerMonomial 1*laurentOrdinaryDerivation (laurentIntegerMonomial (i.val : ℤ))=_
    rw [← laurentEuler_eq_coordinate_mul_ordinary,laurentEuler_nat_monomial]
  have hcomp (i j : Fin (n+1)) :
      constantCompanion n (1 : LaurentSeries K)
        (fun j => HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j)) i j*s j=
          laurentIntegerMonomial ((i.val+1 : ℕ) : ℤ)*A i j := by
    cases i using Fin.lastCases with
    | last =>
      simp only [constantCompanion,Fin.lastCases_last]
      change HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j)*s j=_
      apply mul_left_cancel₀ (polynomialLaurentImage_ne_zero T hT)
      have hc := sameCompanionEulerLastRowSeries_laurent_clearing n T U hT hV j
      change polynomialLaurentImage T*HahnSeries.ofPowerSeries ℤ K
        (sameCompanionEulerLastRowSeries n T U j)=
          laurentIntegerMonomial ((n+1-j.val : ℕ) : ℤ)*polynomialLaurentImage (U (Fin.last n) j) at hc
      rw [← mul_assoc,hc,same_companion_laurent_clearing n c T U hclear]
      change (laurentIntegerMonomial ((n+1-j.val : ℕ) : ℤ)*(polynomialLaurentImage T*A (Fin.last n) j))*
          laurentIntegerMonomial (j.val : ℤ)=_
      have hx : ((n+1-j.val : ℕ) : ℤ)+(j.val : ℤ)=((n+1 : ℕ) : ℤ) := by
        exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt j.isLt)
      calc
        _ = polynomialLaurentImage T*(
          (laurentIntegerMonomial ((n+1-j.val : ℕ) : ℤ)*laurentIntegerMonomial (j.val : ℤ))*A (Fin.last n) j) := by ring
        _ = _ := by rw [laurentIntegerMonomial_mul,hx]; rfl
    | cast i =>
      have hi : i.val+1<n+1 := by omega
      by_cases hj : j=i.succ
      · subst j
        simp [constantCompanion,A,minimalDerivativeCompanion,hi,s,Pi.single_apply]
      · have hjv : j.val≠i.val+1 := by intro h; apply hj; exact Fin.ext h
        simp [constantCompanion,A,minimalDerivativeCompanion,hi,s,Pi.single_apply,hj,hjv]
  funext i j
  apply mul_left_cancel₀ (laurentIntegerMonomial_ne_zero (K:=K) 1)
  apply mul_right_cancel₀ (laurentIntegerMonomial_ne_zero (K:=K) (j.val : ℤ))
  change laurentIntegerMonomial 1*((stage14_laurentAlgebraDerivation (s i)*
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) (LaurentSeries K)) i j+s i*A i j)/s j)*s j=_
  rw [mul_assoc,div_mul_cancel₀ _ (laurentIntegerMonomial_ne_zero _),mul_add,
    ← mul_assoc,hder]
  have hz : laurentIntegerMonomial (K:=K) 1*s i=laurentIntegerMonomial ((i.val+1 : ℕ) : ℤ) := by
    dsimp only [s]
    rw [laurentIntegerMonomial_mul]
    congr 1
    push_cast
    omega
  rw [← mul_assoc (laurentIntegerMonomial 1) (s i),hz,← hcomp]
  have hcancel : laurentIntegerMonomial (K:=K) 1*laurentIntegerMonomial (-1)=1 := by simp
  rw [← mul_assoc (laurentIntegerMonomial 1) (laurentIntegerMonomial (-1)),hcancel,one_mul,
    sameCompanionLaurentEulerMatrix_eq,Matrix.add_apply,add_mul]
  have hdiag : (i.val : LaurentSeries K)*s i*(1 : Matrix (Fin (n+1)) (Fin (n+1)) (LaurentSeries K)) i j=
      Matrix.diagonal (fun j : Fin (n+1) => (j.val : LaurentSeries K)) i j*s j := by
    by_cases hij : i=j
    · subst j; simp [Matrix.one_apply,Matrix.diagonal_apply]
    · simp [Matrix.one_apply,Matrix.diagonal_apply,hij]
  rw [hdiag]
  ring

end StrictEUnit
end
