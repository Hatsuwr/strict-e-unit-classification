import OrdinaryRelationCyclicDichotomy
import StrictEPolynomialCombination
import HomogeneousLiftingFromLinear

/-! Exact reduction of actual linear and homogeneous lifting to the remaining
scalar arithmetic assertion. That assertion is an explicit OPEN premise,
not an axiom, instance, or a conclusion of the rational-coefficient theorem. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

local instance actualCyclicEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

local instance actualCyclicEntireMul (k : Subfield ℂ) : Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

theorem scalar_equation_of_clearing
    {B V ι : Type*} [Field B] [AddCommMonoid V] [Module B V] [Fintype ι]
    (T : B) (hT : T ≠ 0) (a : ι → B) (x : V) (Y : ι → V)
    (h : T • x = ∑ j, a j • Y j) : x = ∑ j, (T⁻¹ * a j) • Y j := by
  calc
    x = T⁻¹ • (T • x) := by rw [smul_smul, inv_mul_cancel₀ hT, one_smul]
    _ = T⁻¹ • (∑ j, a j • Y j) := by rw [h]
    _ = _ := by simp only [Finset.smul_sum, smul_smul]

theorem actualFamily_clearedSystem_normalized
    {ι : Type*} [Fintype ι] (k : Subfield ℂ)
    (F : ι → subfieldEntireFunctionAlgebra k)
    (t : Polynomial k) (B : ι → ι → Polynomial k) (ht : t ≠ 0)
    (hs : ∀ z i, t.eval₂ k.subtype z * deriv (F i).val.val z =
      ∑ j, (B i j).eval₂ k.subtype z * (F j).val.val z) :
    (∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (F i)) =
      ∑ j, ((algebraMap (Polynomial k) (RatFunc k) t)⁻¹ *
        algebraMap (Polynomial k) (RatFunc k) (B i j)) •
        stage14_subfieldEntireLaurentAlgHom k (F j)) ∧
    (∀ i j, algebraMap (Polynomial k) (RatFunc k) (B i j) =
      algebraMap (Polynomial k) (RatFunc k) t *
        ((algebraMap (Polynomial k) (RatFunc k) t)⁻¹ *
          algebraMap (Polynomial k) (RatFunc k) (B i j))) := by
  classical
  let T : RatFunc k := algebraMap (Polynomial k) (RatFunc k) t
  have hT : T ≠ 0 := RatFunc.algebraMap_ne_zero ht
  have hactual (i : ι) :
      Polynomial.aeval (subfieldEntireCoordinate k) t * subfieldEntireFunctionDerivation k (F i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (B i j) * F j := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change stage14_subfieldEntireEvaluation k z
        (Polynomial.aeval (subfieldEntireCoordinate k) t * subfieldEntireFunctionDerivation k (F i)) =
      stage14_subfieldEntireEvaluation k z
        (∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (B i j) * F j)
    rw [map_mul, map_sum, stage14_subfieldEntireEvaluation_polynomial]
    simp_rw [map_mul, stage14_subfieldEntireEvaluation_polynomial]
    exact hs z i
  have hL (i : ι) :
      algebraMap (Polynomial k) (LaurentSeries k) t *
        laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (F i)) =
      ∑ j, algebraMap (Polynomial k) (LaurentSeries k) (B i j) *
        stage14_subfieldEntireLaurentAlgHom k (F j) := by
    have h := congrArg (stage14_subfieldEntireLaurentAlgHom k) (hactual i)
    simpa only [map_mul, map_sum, stage14_subfieldEntireLaurentAlgHom_polynomial,
      stage14_subfieldEntireLaurentAlgHom_derivation] using h
  have hS (i : ι) :
      T • laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (F i)) =
      ∑ j, algebraMap (Polynomial k) (RatFunc k) (B i j) •
        stage14_subfieldEntireLaurentAlgHom k (F j) := by
    simpa only [T, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)] using hL i
  constructor
  · intro i
    exact scalar_equation_of_clearing T hT
      (fun j => algebraMap (Polynomial k) (RatFunc k) (B i j))
      (laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (F i)))
      (fun j => stage14_subfieldEntireLaurentAlgHom k (F j)) (hS i)
  · intro i j
    change _ = T * (T⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hT, one_mul]

theorem actualFamily_polynomialCombination_laurent
    {ι : Type*} [Fintype ι] (k : Subfield ℂ)
    (F : ι → subfieldEntireFunctionAlgebra k)
    (G : subfieldEntireFunctionAlgebra k) (p : ι → Polynomial k)
    (hG : ∀ z : ℂ, G.val.val z = ∑ i, (p i).eval₂ k.subtype z * (F i).val.val z) :
    stage14_subfieldEntireLaurentAlgHom k G =
      ∑ i, algebraMap (Polynomial k) (RatFunc k) (p i) •
        stage14_subfieldEntireLaurentAlgHom k (F i) := by
  classical
  let R : subfieldEntireFunctionAlgebra k :=
    ∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) * F i
  have hR : G = R := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change G.val.val z = stage14_subfieldEntireEvaluation k z R
    dsimp only [R]
    rw [map_sum]
    simp_rw [map_mul, stage14_subfieldEntireEvaluation_polynomial]
    exact hG z
  rw [hR]
  dsimp only [R]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, stage14_subfieldEntireLaurentAlgHom_polynomial, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)]

/-- OPEN scalar arithmetic assertion, retained visibly in every reduction below. -/
def StrictERegularMinimalNonvanishingAtOne : Prop :=
  ∀ (f : ℂ → ℂ) (hf : IsStrictEFunction f), f ≠ 0 →
    ∀ (m : ℕ), 0 < m → ∀ (b : Fin m → RatFunc AlgebraicComplex),
      OrdinaryBorelMinimalCyclicData
        (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (strictEFunctionTaylorRealization f hf)) m b →
      (∀ i, ∃ S : PowerSeries AlgebraicComplex,
        HahnSeries.ofPowerSeries ℤ AlgebraicComplex S = ordinaryPointRationalMap 1 (b i)) →
      f 1 ≠ 0

theorem strictELinearOrdinaryLifting_of_regularMinimalNonvanishing
    (hscalar : StrictERegularMinimalNonvanishingAtOne) : StrictELinearOrdinaryLiftingAtOne := by
  intro n _hn f t B ht hf hs c hc
  classical
  letI : SMul (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex) := Algebra.toSMul
  letI : Module (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex) := Algebra.toModule
  letI : HSMul (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex)
      (LaurentSeries AlgebraicComplex) := ⟨fun a x => algebraMap _ _ a * x⟩
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let F : Fin n → subfieldEntireFunctionAlgebra k :=
    fun i => strictEFunctionTaylorRealization (f i).val (hf i)
  let Y : Fin n → LaurentSeries AlgebraicComplex :=
    fun i => stage14_subfieldEntireLaurentAlgHom k (F i)
  let A : Fin n → Fin n → RatFunc AlgebraicComplex := fun i j =>
    (algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) t)⁻¹ *
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (B i j)
  have ht0 : t ≠ 0 := by intro h; apply ht; simp [h]
  have hsys := actualFamily_clearedSystem_normalized k F t B ht0 hs
  have hY : ∀ i, laurentOrdinaryDerivation (Y i) = ∑ j, A i j • Y j := hsys.1
  have hclear : ∀ i j,
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (B i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) t * A i j := hsys.2
  rcases ordinary_relation_or_prescribed_regular_minimal
      (1 : AlgebraicComplex) Y A hY t B ht hclear c with hrel | hcyc
  · obtain ⟨p, hp, hpc⟩ := hrel
    refine ⟨p, hpc, ?_⟩
    exact (actualFamily_polynomial_relation_iff k F p).mp hp
  · obtain ⟨m, hm, _hmn, p, hp, b, hmin, hreg⟩ := hcyc
    let g : ℂ → ℂ := fun z => ∑ i,
      (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * (f i).val z
    have hg : IsStrictEFunction g := strictEFunction_polynomialCombination p (fun i => (f i).val) hf
    let G := strictEFunctionTaylorRealization g hg
    have himage : stage14_subfieldEntireLaurentAlgHom k G =
        ∑ i, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (p i) • Y i :=
      actualFamily_polynomialCombination_laurent k F G p (fun z => rfl)
    have hminG : OrdinaryBorelMinimalCyclicData (stage14_subfieldEntireLaurentAlgHom k G) m b := by
      rw [himage]
      exact hmin
    have hLne : stage14_subfieldEntireLaurentAlgHom k G ≠ 0 := by
      have h := hminG.1.ne_zero (⟨0, hm⟩ : Fin m)
      simpa using h
    have hgne : g ≠ 0 := by
      intro h
      apply hLne
      have hG : G = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        exact h
      rw [hG, map_zero]
    have hvalue : g 1 = 0 := by
      dsimp only [g]
      simp_rw [Polynomial.eval₂_at_one, hp]
      exact hc
    exact False.elim ((hscalar g hg hgne m hm b hminG hreg) hvalue)

theorem homogeneousOrdinaryLifting_of_regularMinimalNonvanishing
    (hscalar : StrictERegularMinimalNonvanishingAtOne) :
    HomogeneousOrdinaryLiftingAtOne IsStrictEFunction :=
  homogeneousOrdinaryLifting_of_linear (strictELinearOrdinaryLifting_of_regularMinimalNonvanishing hscalar)

theorem strictELaurentLifting_of_regularMinimalNonvanishing
    (hscalar : StrictERegularMinimalNonvanishingAtOne) : StrictELaurentRelationLifting :=
  strictELaurentLifting_of_linear (strictELinearOrdinaryLifting_of_regularMinimalNonvanishing hscalar)
end StrictEUnit
