import StrictECoefficientConjugation
import GaloisPowerSeriesProduct
import Stage26StrictEFiniteCoefficientField
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Actual finite Galois products of coefficient-conjugate strict E-functions.
Lifts are used only for strict-E closure. Product invariance is proved inside
one finite normal coefficient field; vanishing uses only the identity factor. -/
noncomputable section

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open scoped BigOperators

namespace StrictEUnit
attribute [local instance 2000] Algebra.toModule

local instance actualNormEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

/-- Literal product of the functions reconstructed from the conjugate
factorial coefficients. No automorphism is applied to complex values. -/
def strictEGaloisNormFunction
    (K : IntermediateField ℚ AlgebraicComplex)
    [Fintype (K ≃ₐ[ℚ] K)] (a : ℕ → K) : ℂ → ℂ :=
  fun z =>
    ∏ σ : K ≃ₐ[ℚ] K,
      stage41_strictSeriesFunction
        (fun n => (σ (a n) : AlgebraicComplex)) z

theorem finiteGalois_product_coeff_rational
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    [Fintype (K ≃ₐ[ℚ] K)] (x : PowerSeries K) (n : ℕ) :
    ∃ q : ℚ, algebraMap ℚ K q = PowerSeries.coeff K n
      (∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom x) := by
  apply powerSeries_prod_coeff_rational_of_permuted
    (fun σ : K ≃ₐ[ℚ] K => PowerSeries.map σ.toRingHom x) _ n
  intro τ
  refine ⟨Equiv.mulLeft τ, ?_⟩
  intro σ
  ext j
  simp only [PowerSeries.coeff_map]
  rfl

theorem actualStrictE_galoisNorm_realization
    (K : IntermediateField ℚ AlgebraicComplex) [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K)
    (hc : ∀ σ : K ≃ₐ[ℚ] K, HasStrictEArithmetic (fun n => (σ (a n) : AlgebraicComplex))) :
    ∃ G : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      G.val.val = strictEGaloisNormFunction K a ∧
      subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield G =
        PowerSeries.map K.val.toRingHom
          (∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom
            (PowerSeries.mk (fun n => a n / (n.factorial : K)))) := by
  classical
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let c : (K ≃ₐ[ℚ] K) → ℕ → AlgebraicComplex := fun σ n => (σ (a n) : AlgebraicComplex)
  let B : (K ≃ₐ[ℚ] K) → subfieldEntireFunctionAlgebra k :=
    fun σ => stage41_strictSeriesRealization (c σ) (hc σ)
  refine ⟨∏ σ, B σ, ?_, ?_⟩
  · funext z
    change stage14_subfieldEntireEvaluation k z (∏ σ, B σ) =
      ∏ σ, stage14_subfieldEntireEvaluation k z (B σ)
    exact map_prod _ _ _
  · rw [map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro σ _
    change subfieldEntireTaylorAlgHom k
        (stage41_strictSeriesRealization (c σ) (hc σ)) = _
    rw [stage41_strictSeries_taylor]
    ext n
    simp only [PowerSeries.coeff_map, stage41_coeff_strictFormalSeries,
      PowerSeries.coeff_mk, map_div₀, map_natCast]
    rfl

/-- A genuine finite Galois coefficient product is strict E, has rational
factorial coefficients, preserves nonzeroness, and inherits a zero at 1
from its identity factor. -/
theorem actualStrictE_galoisNorm_properties
    (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K)
    {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (hs : ∀ z : ℂ,
      HasSum
        (fun n =>
          ((a n : AlgebraicComplex) : ℂ) *
            z ^ n / (n.factorial : ℂ))
        (f z)) :
    IsStrictEFunction (strictEGaloisNormFunction K a) ∧
      (∃ r : ℕ → ℚ, ∀ z : ℂ,
        HasSum
          (fun n => (r n : ℂ) * z ^ n / (n.factorial : ℂ))
          (strictEGaloisNormFunction K a z)) ∧
      (f ≠ 0 → strictEGaloisNormFunction K a ≠ 0) ∧
      (f 1 = 0 → strictEGaloisNormFunction K a 1 = 0) := by
  classical
  let aA : ℕ → AlgebraicComplex :=
    fun n => (a n : AlgebraicComplex)
  let c : (K ≃ₐ[ℚ] K) → ℕ → AlgebraicComplex :=
    fun σ n => (σ (a n) : AlgebraicComplex)

  have ha : HasStrictEArithmetic aA :=
    (stage41_actualStrictE_isStrictESeries hf aA hs).1

  -- Only restriction compatibility is used here. There is no claim that
  -- the arbitrarily selected lifts form a group homomorphism.
  have hext (σ : K ≃ₐ[ℚ] K) :
      (fun n =>
        (σ.toAlgHom.liftNormal AlgebraicComplex) (aA n)) =
        c σ := by
    funext n
    exact σ.toAlgHom.liftNormal_commutes AlgebraicComplex (a n)

  have hc (σ : K ≃ₐ[ℚ] K) :
      HasStrictEArithmetic (c σ) := by
    rw [← hext σ]
    exact strictEArithmetic_map
      (σ.toAlgHom.liftNormal AlgebraicComplex) ha

  have hstrict (σ : K ≃ₐ[ℚ] K) :
      IsStrictEFunction (stage41_strictSeriesFunction (c σ)) := by
    have h :=
      actualStrictE_coefficient_conjugate
        (σ.toAlgHom.liftNormal AlgebraicComplex) hf aA hs
    rw [hext σ] at h
    exact h

  have hg :
      IsStrictEFunction (strictEGaloisNormFunction K a) := by
    simpa only [strictEGaloisNormFunction, c] using
      strictEFunction_finsetProd
        (Finset.univ : Finset (K ≃ₐ[ℚ] K))
        (fun σ => stage41_strictSeriesFunction (c σ))
        (fun σ _ => hstrict σ)

  let k := (algebraicClosure ℚ ℂ).toSubfield
  let x : PowerSeries K := PowerSeries.mk (fun n => a n / (n.factorial : K))
  let P : PowerSeries K := ∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom x
  obtain ⟨G, hGval, hT⟩ := actualStrictE_galoisNorm_realization K a hc
  have hrat (n : ℕ) :
      ∃ q : ℚ, algebraMap ℚ K q = PowerSeries.coeff K n P :=
    finiteGalois_product_coeff_rational x n
  choose q hq using hrat

  have hcoeffA (n : ℕ) :
      PowerSeries.coeff AlgebraicComplex n
          (subfieldEntireTaylorAlgHom k G) =
        algebraMap ℚ AlgebraicComplex (q n) := by
    rw [hT, PowerSeries.coeff_map, ← hq n]
    exact K.val.commutes (q n)

  have hcoeffC (n : ℕ) :
      entireCauchyCoefficient (strictEGaloisNormFunction K a) n =
        (q n : ℂ) := by
    have hh :=
      congrArg (algebraicClosure ℚ ℂ).val (hcoeffA n)
    have hh' :
        entireCauchyCoefficient G.val.val n = (q n : ℂ) := by
      simpa only [
        subfieldEntireTaylorAlgHom_apply,
        subfieldEntireTaylorSeries,
        PowerSeries.coeff_mk,
        AlgHom.commutes
      ] using hh
    simpa only [hGval] using hh'

  have hr :
      ∃ r : ℕ → ℚ, ∀ z : ℂ,
        HasSum
          (fun n => (r n : ℂ) * z ^ n / (n.factorial : ℂ))
          (strictEGaloisNormFunction K a z) := by
    refine ⟨fun n => q n * (n.factorial : ℚ), ?_⟩
    intro z
    convert
      entireCauchyCoefficient_hasSum
        (strictEFunction_differentiable hg) z using 1
    funext n
    rw [hcoeffC n]
    have hn : (n.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    push_cast
    field_simp [hn] <;> ring

  refine ⟨hg, hr, ?_, ?_⟩
  · intro hfne hgzero
    have hx : x ≠ 0 := by
      intro hxzero
      have hazero (n : ℕ) : a n = 0 := by
        have hh :=
          congrArg (PowerSeries.coeff K n) hxzero
        have hh' : a n / (n.factorial : K) = 0 := by
          simpa only [x, PowerSeries.coeff_mk, map_zero] using hh
        exact (div_eq_zero_iff.mp hh').resolve_right
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      apply hfne
      funext z
      have hz : HasSum (fun _ : ℕ => (0 : ℂ)) (f z) := by
        simpa [hazero] using hs z
      exact hz.unique hasSum_zero

    have hP : P ≠ 0 := by
      change
        (∏ σ : K ≃ₐ[ℚ] K,
          PowerSeries.map σ.toRingHom x) ≠ 0
      apply Finset.prod_ne_zero_iff.mpr
      intro σ _
      intro hzero
      apply hx
      apply PowerSeries.map_injective σ.toRingHom σ.injective
      simpa only [map_zero] using hzero

    have hGzero : G = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hGval.trans hgzero

    apply hP
    apply PowerSeries.map_injective K.val.toRingHom K.val.injective
    rw [map_zero, ← hT, hGzero, map_zero]

  · intro hfzero
    have hid : c (1 : K ≃ₐ[ℚ] K) = aA := by
      funext n
      rfl
    have hidfun :
        stage41_strictSeriesFunction (c (1 : K ≃ₐ[ℚ] K)) =
          f := by
      rw [hid]
      exact stage41_strictSeriesFunction_eq_of_representation ha f hs
    change
      (∏ σ : K ≃ₐ[ℚ] K,
        stage41_strictSeriesFunction (c σ) 1) = 0
    apply Finset.prod_eq_zero
      (Finset.mem_univ (1 : K ≃ₐ[ℚ] K))
    rw [hidfun, hfzero]

/-- The finite Galois field may also contain any specified finite family
of algebraic polynomials, for later operator arguments. -/
theorem actualStrictE_finiteGalois_field_enlarge_polynomials
    {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (p : ι → Polynomial AlgebraicComplex) :
    ∃ K : IntermediateField ℚ AlgebraicComplex,
      FiniteDimensional ℚ K ∧
      IsGalois ℚ K ∧
      ∃ a : ℕ → AlgebraicComplex,
        (∀ n, a n ∈ K) ∧
        (∀ i j, (p i).coeff j ∈ K) ∧
        (∀ z : ℂ,
          HasSum
            (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ))
            (f z)) ∧
        HasStrictEArithmetic a := by
  obtain ⟨F, hF, a, ha, hs, harith⟩ :=
    stage26_strictE_fixed_field_series hf
  obtain ⟨E, hE, hFE, hp⟩ :=
    stage26_finite_coefficient_field_enlarge_polynomials F hF p
  letI : FiniteDimensional ℚ E := hE
  let K : IntermediateField ℚ AlgebraicComplex :=
    IntermediateField.normalClosure ℚ E AlgebraicComplex
  have hEK : E ≤ K := IntermediateField.le_normalClosure E
  refine ⟨K, inferInstance, inferInstance, a, ?_, ?_, hs, harith⟩
  · intro n
    exact hEK (hFE (ha n))
  · intro i j
    exact hEK (hp i j)

/-- Unconditional construction from the unchanged actual strict-E predicate.
The constructed function is the literal norm product defined above. -/
theorem actualStrictE_exists_rational_galoisNorm
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    ∃ g : ℂ → ℂ,
      IsStrictEFunction g ∧
      (∃ r : ℕ → ℚ, ∀ z : ℂ,
        HasSum
          (fun n => (r n : ℂ) * z ^ n / (n.factorial : ℂ))
          (g z)) ∧
      (f ≠ 0 → g ≠ 0) ∧
      (f 1 = 0 → g 1 = 0) := by
  obtain ⟨F, hF, a, ha, hs, _⟩ :=
    stage26_strictE_fixed_field_series hf
  letI : FiniteDimensional ℚ F := hF
  let K : IntermediateField ℚ AlgebraicComplex :=
    IntermediateField.normalClosure ℚ F AlgebraicComplex
  letI : FiniteDimensional ℚ K := inferInstance
  letI : IsGalois ℚ K := inferInstance
  letI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  let b : ℕ → K :=
    fun n => ⟨a n, IntermediateField.le_normalClosure F (ha n)⟩
  have hbs : ∀ z : ℂ,
      HasSum
        (fun n =>
          ((b n : AlgebraicComplex) : ℂ) *
            z ^ n / (n.factorial : ℂ))
        (f z) := hs
  exact ⟨strictEGaloisNormFunction K b,
    actualStrictE_galoisNorm_properties K b hf hbs⟩

end StrictEUnit
