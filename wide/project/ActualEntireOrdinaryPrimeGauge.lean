import ActualEntireAbsolutePrimality
import OrdinaryPointPolynomialIdealGauge

/-! The source relation ideal is the literal functional kernel of the supplied
actual entire family. Its translated gauge is prime and descends to constants,
using the same rational system, common clearing polynomial, and fixed point one. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit
attribute [local instance 2000] Algebra.toModule

local instance actualGaugeEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance actualGaugeEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

local instance actualGaugeEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

def actualEntireRelationIdeal (k : Subfield ℂ) {σ : Type*}
    (f : σ → subfieldEntireFunctionAlgebra k) : Ideal (MvPolynomial σ (RatFunc k)) :=
  mvFunctionalIdeal (algebraMap (RatFunc k) (LaurentSeries k))
    (fun i => stage14_subfieldEntireLaurentAlgHom k (f i))

theorem actualEntireRelationIdeal_stable
    (k : Subfield ℂ) {r : ℕ} (f : Fin r → subfieldEntireFunctionAlgebra k)
    (A : Matrix (Fin r) (Fin r) (RatFunc k))
    (hsystem : ∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (f i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        stage14_subfieldEntireLaurentAlgHom k (f j)) :
    ∀ P, P ∈ actualEntireRelationIdeal k f →
      mvSystemD (rationalOrdinaryAddDerivative (K := k)) A P ∈ actualEntireRelationIdeal k f := by
  exact mvFunctionalIdeal_stable
    (rationalOrdinaryAddDerivative (K := k)) (laurentOrdinaryAddDerivative (K := k))
    rationalOrdinaryAddDerivative_one rationalOrdinaryAddDerivative_mul
    laurentOrdinaryAddDerivative_mul (algebraMap (RatFunc k) (LaurentSeries k))
    stage14_rationalLaurent_differential A
    (fun i => stage14_subfieldEntireLaurentAlgHom k (f i)) hsystem

/-- The exact actual entire cleared differential system gives the rational
Laurent system for the same functions and coefficients. -/
theorem actualEntire_cleared_system_to_laurent
    (k : Subfield ℂ) {r : ℕ} (f : Fin r → subfieldEntireFunctionAlgebra k)
    (A : Matrix (Fin r) (Fin r) (RatFunc k))
    (t : Polynomial k) (U : Matrix (Fin r) (Fin r) (Polynomial k)) (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
      algebraMap (Polynomial k) (RatFunc k) t * A i j)
    (hactual : ∀ i,
      Polynomial.aeval (subfieldEntireCoordinate k) t * subfieldEntireFunctionDerivation k (f i) =
        ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (U i j) * f j) :
    ∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (f i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        stage14_subfieldEntireLaurentAlgHom k (f j) := by
  have ht0 : t ≠ 0 := by
    intro h
    apply ht
    rw [h, Polynomial.eval_zero]
  have hT : algebraMap (Polynomial k) (LaurentSeries k) t ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)]
    exact (map_ne_zero (algebraMap (RatFunc k) (LaurentSeries k))).mpr (RatFunc.algebraMap_ne_zero ht0)
  have hclearL (i j : Fin r) :
      algebraMap (Polynomial k) (LaurentSeries k) (U i j) =
        algebraMap (Polynomial k) (LaurentSeries k) t *
          algebraMap (RatFunc k) (LaurentSeries k) (A i j) := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply
      (Polynomial k) (RatFunc k) (LaurentSeries k)] using
      congrArg (algebraMap (RatFunc k) (LaurentSeries k)) (hclear i j)
  intro i
  have h := congrArg (stage14_subfieldEntireLaurentAlgHom k) (hactual i)
  simp only [map_mul, map_sum, stage14_subfieldEntireLaurentAlgHom_polynomial,
    stage14_subfieldEntireLaurentAlgHom_derivation] at h
  apply mul_left_cancel₀ hT
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hclearL, mul_assoc]

/-- No relative closure, absolute-primality, differential-ideal stability or
fundamental matrix is supplied: those conclusions are derived from the source. -/
theorem actualEntireOrdinaryPrimeGauge_atOne
    (k : Subfield ℂ) {r : ℕ} (f : Fin r → subfieldEntireFunctionAlgebra k)
    (A : Matrix (Fin r) (Fin r) (RatFunc k))
    (hsystem : ∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (f i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        stage14_subfieldEntireLaurentAlgHom k (f j))
    (t : Polynomial k) (U : Matrix (Fin r) (Fin r) (Polynomial k)) (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
      algebraMap (Polynomial k) (RatFunc k) t * A i j) :
    let W := ordinaryPointLaurentFundamental t U (1 : k)
    let J := ordinaryPointGaugedIdeal t U (1 : k) (actualEntireRelationIdeal k f)
    let c := MvPolynomial.map (algebraMap k (LaurentSeries k))
    IsUnit W ∧ W.map (fun x : LaurentSeries k => x.coeff 0) = 1 ∧
      W.map (laurentOrdinaryAddDerivative (K := k)) =
        A.map (ordinaryPointRationalMap (1 : k)) * W ∧
      J.IsPrime ∧ (J.comap c).IsPrime ∧ (J.comap c).map c = J := by
  dsimp only
  obtain ⟨hu, hzero, hder⟩ := ordinaryPointLaurentFundamental_atOne A t U ht hclear
  have hp : ((actualEntireRelationIdeal k f).map
      (MvPolynomial.map (ordinaryPointRationalMap (1 : k)))).IsPrime :=
    actual_entire_relation_ideal_map_ringHom_isPrime k f (ordinaryPointRationalMap (1 : k))
  have hJ := ordinaryPointGaugedIdeal_isPrime t U (1 : k) (actualEntireRelationIdeal k f) hp
  letI := hJ
  exact ⟨hu, hzero, hder, hJ, Ideal.comap_isPrime _ _,
    ordinaryPointGaugedIdeal_atOne_constant_descent A t U ht hclear
      (actualEntireRelationIdeal k f) (actualEntireRelationIdeal_stable k f A hsystem)⟩

end StrictEUnit
