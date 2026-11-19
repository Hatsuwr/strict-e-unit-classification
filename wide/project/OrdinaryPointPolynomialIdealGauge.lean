import MatrixPolynomialDifferentialGauge
import OrdinaryPointFundamentalCoefficients

/-! At the specified ordinary point, the literal normalized fundamental matrix
constructs the gauge; differential stability descends the resulting ideal. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def laurentOrdinaryAddDerivative : LaurentSeries K →+ LaurentSeries K :=
  { toFun := fun x => laurentOrdinaryDerivation x
    map_zero' := (laurentOrdinaryDerivation (k := K)).map_zero
    map_add' := fun x y => (laurentOrdinaryDerivation (k := K)).map_add x y }

@[simp] theorem laurentOrdinaryAddDerivative_apply (x : LaurentSeries K) :
    laurentOrdinaryAddDerivative x = laurentOrdinaryDerivation x := rfl

theorem laurentOrdinaryAddDerivative_one :
    laurentOrdinaryAddDerivative (K := K) 1 = 0 :=
  (laurentOrdinaryDerivation (k := K)).map_one_eq_zero

theorem laurentOrdinaryAddDerivative_mul (x y : LaurentSeries K) :
    laurentOrdinaryAddDerivative (x * y) =
      x * laurentOrdinaryAddDerivative y + y * laurentOrdinaryAddDerivative x :=
  (laurentOrdinaryDerivation (k := K)).leibniz x y

@[simp] theorem mvCoeffD_laurentOrdinaryAddDerivative {σ : Type*} :
    mvCoeffD (σ := σ) (laurentOrdinaryAddDerivative (K := K)) =
      laurentMvCoeffDerivative := rfl

def rationalOrdinaryAddDerivative : RatFunc K →+ RatFunc K :=
  { toFun := fun x => stage14_rationalOrdinaryDerivation x
    map_zero' := (stage14_rationalOrdinaryDerivation (k := K)).map_zero
    map_add' := fun x y => (stage14_rationalOrdinaryDerivation (k := K)).map_add x y }

@[simp] theorem rationalOrdinaryAddDerivative_apply (x : RatFunc K) :
    rationalOrdinaryAddDerivative x = stage14_rationalOrdinaryDerivation x := rfl

theorem rationalOrdinaryAddDerivative_one :
    rationalOrdinaryAddDerivative (K := K) 1 = 0 :=
  (stage14_rationalOrdinaryDerivation (k := K)).map_one_eq_zero

theorem rationalOrdinaryAddDerivative_mul (x y : RatFunc K) :
    rationalOrdinaryAddDerivative (x * y) =
      x * rationalOrdinaryAddDerivative y + y * rationalOrdinaryAddDerivative x :=
  (stage14_rationalOrdinaryDerivation (k := K)).leibniz x y

theorem ordinaryPointRationalMap_addDerivative (α : K) (x : RatFunc K) :
    laurentOrdinaryAddDerivative (ordinaryPointRationalMap α x) =
      ordinaryPointRationalMap α (rationalOrdinaryAddDerivative x) :=
  ordinaryPointRationalMap_derivative α x

variable {r : ℕ}

theorem ordinaryPointClearedMatrix_map
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j) :
    (ordinaryPointClearedMatrix t U α).map (HahnSeries.ofPowerSeries ℤ K) =
      A.map (ordinaryPointRationalMap α) := by
  apply Matrix.ext
  intro i j
  change HahnSeries.ofPowerSeries ℤ K
      (ordinaryPointPolynomialSeries α (U i j) * (ordinaryPointPolynomialSeries α t)⁻¹) =
    ordinaryPointRationalMap α (A i j)
  exact (ordinaryPointRationalMap_of_clearing
    α (A i j) t (U i j) hα (hclear i j)).symm

/-- Constructed from the same ordinary system, not an assumed matrix of solutions. -/
def ordinaryPointLaurentFundamental
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) : Matrix (Fin r) (Fin r) (LaurentSeries K) :=
  (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)).map
    (HahnSeries.ofPowerSeries ℤ K)

theorem ordinaryPointLaurentFundamental_isUnit
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) :
    IsUnit (ordinaryPointLaurentFundamental t U α) := by
  exact (formalFundamentalMatrix_isUnit (ordinaryPointClearedMatrix t U α)).map
    (HahnSeries.ofPowerSeries ℤ K).mapMatrix

/-- This coefficient identity is proved from power series; coefficient zero is
not claimed to be a ring homomorphism on arbitrary Laurent series. -/
theorem ordinaryPointLaurentFundamental_coeff_zero
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) :
    (ordinaryPointLaurentFundamental t U α).map
      (fun f : LaurentSeries K => f.coeff 0) = 1 := by
  apply Matrix.ext
  intro i j
  change (HahnSeries.ofPowerSeries ℤ K
      (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j)).coeff
        ((0 : ℕ) : ℤ) = (1 : Matrix (Fin r) (Fin r) K) i j
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j)
    (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U α))
  simpa only [Matrix.map_apply, PowerSeries.coeff_zero_eq_constantCoeff] using h

theorem ordinaryPointLaurentFundamental_derivative
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j) :
    (ordinaryPointLaurentFundamental t U α).map (laurentOrdinaryAddDerivative (K := K)) =
      A.map (ordinaryPointRationalMap α) * ordinaryPointLaurentFundamental t U α := by
  let B := ordinaryPointClearedMatrix t U α
  let Z := formalFundamentalMatrix B
  let ψ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  have hB : B.map ψ = A.map (ordinaryPointRationalMap α) :=
    ordinaryPointClearedMatrix_map A t U α hα hclear
  apply Matrix.ext
  intro i j
  change laurentOrdinaryDerivation (ψ (Z i j)) =
    (A.map (ordinaryPointRationalMap α) * Z.map ψ) i j
  calc
    _ = ψ (PowerSeries.derivative K (Z i j)) :=
      laurentOrdinaryDerivation_ofPowerSeries (Z i j)
    _ = ψ ((B * Z) i j) := by
      apply congrArg ψ
      exact congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => M i j)
        (formalFundamentalMatrix_derivative B)
    _ = (B.map ψ * Z.map ψ) i j := RingHom.map_matrix_mul B Z i j ψ
    _ = _ := by rw [hB]

theorem ordinaryPointLaurentFundamental_atOne
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j) :
    let W := ordinaryPointLaurentFundamental t U (1 : K)
    IsUnit W ∧ W.map (fun f : LaurentSeries K => f.coeff 0) = 1 ∧
      W.map (laurentOrdinaryAddDerivative (K := K)) =
        A.map (ordinaryPointRationalMap (1 : K)) * W := by
  exact ⟨ordinaryPointLaurentFundamental_isUnit t U 1,
    ordinaryPointLaurentFundamental_coeff_zero t U 1,
    ordinaryPointLaurentFundamental_derivative A t U 1 ht hclear⟩

def ordinaryPointGaugedIdeal (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (I : Ideal (MvPolynomial (Fin r) (RatFunc K))) :
    Ideal (MvPolynomial (Fin r) (LaurentSeries K)) :=
  (I.map (MvPolynomial.map (ordinaryPointRationalMap α))).map
    (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)).toRingHom

theorem ordinaryPointGaugedIdeal_stable
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (I : Ideal (MvPolynomial (Fin r) (RatFunc K)))
    (hI : ∀ P, P ∈ I → mvSystemD (rationalOrdinaryAddDerivative (K := K)) A P ∈ I) :
    ∀ P, P ∈ ordinaryPointGaugedIdeal t U α I →
      laurentMvCoeffDerivative P ∈ ordinaryPointGaugedIdeal t U α I := by
  have hIL := mvSystemD_ideal_map_stable
    (rationalOrdinaryAddDerivative (K := K)) (laurentOrdinaryAddDerivative (K := K))
    rationalOrdinaryAddDerivative_one laurentOrdinaryAddDerivative_one
    rationalOrdinaryAddDerivative_mul laurentOrdinaryAddDerivative_mul
    (ordinaryPointRationalMap α) (ordinaryPointRationalMap_addDerivative α) A I hI
  have hJ := matrixPolynomialSubst_ideal_stable
    (laurentOrdinaryAddDerivative (K := K)) laurentOrdinaryAddDerivative_one
    laurentOrdinaryAddDerivative_mul (A.map (ordinaryPointRationalMap α))
    (ordinaryPointLaurentFundamental t U α)
    (ordinaryPointLaurentFundamental_derivative A t U α hα hclear)
    (I.map (MvPolynomial.map (ordinaryPointRationalMap α))) hIL
  intro P hP
  have h := hJ P hP
  rw [mvCoeffD_laurentOrdinaryAddDerivative] at h
  exact h

theorem ordinaryPointGaugedIdeal_atOne_constant_descent
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (I : Ideal (MvPolynomial (Fin r) (RatFunc K)))
    (hI : ∀ P, P ∈ I → mvSystemD (rationalOrdinaryAddDerivative (K := K)) A P ∈ I) :
    let J := ordinaryPointGaugedIdeal t U (1 : K) I
    (J.comap (MvPolynomial.map (algebraMap K (LaurentSeries K)))).map
      (MvPolynomial.map (algebraMap K (LaurentSeries K))) = J := by
  exact laurent_stable_polynomial_ideal_constant_descent
    (ordinaryPointGaugedIdeal t U (1 : K) I)
    (ordinaryPointGaugedIdeal_stable A t U 1 ht hclear I hI)

/-- Primality is preserved by the constructed invertible matrix substitution.
The separately proved source theorem will provide the extension's primality. -/
theorem ordinaryPointGaugedIdeal_isPrime
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (I : Ideal (MvPolynomial (Fin r) (RatFunc K)))
    (hI : (I.map (MvPolynomial.map (ordinaryPointRationalMap α))).IsPrime) :
    (ordinaryPointGaugedIdeal t U α I).IsPrime := by
  classical
  letI := hI
  obtain ⟨u, hu⟩ := ordinaryPointLaurentFundamental_isUnit t U α
  change ((I.map (MvPolynomial.map (ordinaryPointRationalMap α))).map
    (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)).toRingHom).IsPrime
  rw [← hu]
  exact Ideal.map_isPrime_of_equiv (matrixPolynomialGaugeEquiv u)

end StrictEUnit
end
