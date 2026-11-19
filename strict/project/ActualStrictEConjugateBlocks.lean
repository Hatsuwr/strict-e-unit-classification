import CoefficientConjugatePrefix
import ActualStrictEGaloisNorm
import Mathlib.Algebra.MvPolynomial.Eval

/-! Literal finite conjugate blocks of one actual minimal strict-E prefix.
The ordinary clearing and minimal data are those of the original source.
Conjugate independence, block equations, a common ordinary denominator, and
the identity/product links are conclusions, not additional premises. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
local instance conjugateBlockCoefficientSemiring : Semiring AlgebraicComplex :=
  (inferInstance : Field AlgebraicComplex).toSemiring
attribute [local instance 2000] Algebra.toModule
theorem exists_normal_coefficient_automorphism
    {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    [Normal F E] (σ : B ≃ₐ[F] B) :
    ∃ τ : E ≃ₐ[F] E, ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x) := by
  exact ⟨σ.liftNormal E, σ.liftNormal_commutes E⟩

@[irreducible] noncomputable def strictEGaloisCoefficientLift (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (σ : K ≃ₐ[ℚ] K) :
    AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex :=
  Classical.choose (exists_normal_coefficient_automorphism (E := AlgebraicComplex) σ)

theorem strictEGaloisCoefficientLift_commutes (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (σ : K ≃ₐ[ℚ] K) (x : K) :
    strictEGaloisCoefficientLift K σ (x : AlgebraicComplex) = (σ x : AlgebraicComplex) := by
  unfold strictEGaloisCoefficientLift
  exact Classical.choose_spec (exists_normal_coefficient_automorphism (E := AlgebraicComplex) σ) x

def algebraicCoefficientPolynomialMap
    (τ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (p : Polynomial AlgebraicComplex) :
    Polynomial AlgebraicComplex := p.map τ.toAlgHom.toRingHom

def algebraicCoefficientRationalMap
    (τ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (q : RatFunc AlgebraicComplex) :
    RatFunc AlgebraicComplex := coefficientRatFuncHom τ.toAlgHom.toRingHom q

local instance conjugateBlockEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance conjugateBlockEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

local instance conjugateBlockEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

/-- Enlarge around the already chosen source coefficients, rather than changing
the coefficient sequence used in the original minimal-prefix construction. -/
theorem actualStrictE_same_coefficients_finiteGalois_clearing_field
    {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z))
    {r : ℕ} (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex)) :
    ∃ K : IntermediateField ℚ AlgebraicComplex,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
      (∀ n, a n ∈ K) ∧ (∀ n, T.coeff n ∈ K) ∧
      (∀ i j n, (U i j).coeff n ∈ K) := by
  let p : Option (Fin r × Fin r) → Polynomial AlgebraicComplex :=
    fun s => match s with | none => T | some ij => U ij.1 ij.2
  obtain ⟨K, hK, hG, a', ha', hp, hs', _harith⟩ :=
    actualStrictE_finiteGalois_field_enlarge_polynomials hf p
  have heq : a' = a := stage41_factorialSeries_coefficients_unique
    (strictEFunction_differentiable hf) a' a hs' hs
  refine ⟨K, hK, hG, ?_, ?_, ?_⟩
  · intro n
    simpa only [heq] using ha' n
  · intro n
    exact hp none n
  · intro i j n
    exact hp (some (i, j)) n

/-- Blockwise multiplication by the complementary denominator gives the
actual entire system for the one common denominator. -/
theorem finiteBlock_actual_cleared
    {S : Type*} [Fintype S] [DecidableEq S] {r : ℕ}
    (k : Subfield ℂ) (f : S → Fin r → subfieldEntireFunctionAlgebra k)
    (T : S → Polynomial k) (U : S → Matrix (Fin r) (Fin r) (Polynomial k))
    (hs : ∀ s i, Polynomial.aeval (subfieldEntireCoordinate k) (T s) *
        subfieldEntireFunctionDerivation k (f s i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (U s i j) * f s j) :
    ∀ i : Fin r × S,
      Polynomial.aeval (subfieldEntireCoordinate k) (finiteBlockClearingPolynomial T) *
        subfieldEntireFunctionDerivation k (f i.2 i.1) =
      ∑ j : Fin r × S,
        Polynomial.aeval (subfieldEntireCoordinate k)
          (Matrix.blockDiagonal (fun s i j => finiteBlockClearingMultiplier T s * U s i j) i j) *
        f j.2 j.1 := by
  rintro ⟨i, s⟩
  rw [← finiteBlockClearingMultiplier_mul T s, map_mul, mul_assoc, hs s i,
    Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.blockDiagonal_apply, apply_ite, map_mul, map_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_assoc]

section GaloisBlocks
variable (K : IntermediateField ℚ AlgebraicComplex)
  [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]

def strictEGaloisBlockFamily (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex))) (r : ℕ) :
    Fin r × (K ≃ₐ[ℚ] K) → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
  fun i => actualConjugateDerivativePrefix (fun n => (a n : AlgebraicComplex)) ha
    (strictEGaloisCoefficientLift K i.2) r i.1

def strictEGaloisBlockDenominator (T : Polynomial AlgebraicComplex) :
    (K ≃ₐ[ℚ] K) → Polynomial AlgebraicComplex :=
  fun σ => algebraicCoefficientPolynomialMap (strictEGaloisCoefficientLift K σ) T

def strictEGaloisCommonClearing (T : Polynomial AlgebraicComplex) : Polynomial AlgebraicComplex :=
  finiteBlockClearingPolynomial (strictEGaloisBlockDenominator K T)

def strictEGaloisBlockCompanion (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex) :
    Matrix (Fin r × (K ≃ₐ[ℚ] K)) (Fin r × (K ≃ₐ[ℚ] K)) (RatFunc AlgebraicComplex) := by
  classical
  exact Matrix.blockDiagonal (fun σ : K ≃ₐ[ℚ] K =>
    minimalDerivativeCompanion r (fun j => coefficientRatFuncHom
      (strictEGaloisCoefficientLift K σ).toAlgHom.toRingHom (b j)))

def strictEGaloisClearedBlockMatrix {r : ℕ} (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex)) :
    Matrix (Fin r × (K ≃ₐ[ℚ] K)) (Fin r × (K ≃ₐ[ℚ] K)) (Polynomial AlgebraicComplex) := by
  classical
  exact Matrix.blockDiagonal (fun (σ : K ≃ₐ[ℚ] K) (i j : Fin r) =>
    finiteBlockClearingMultiplier (strictEGaloisBlockDenominator K T) σ *
      algebraicCoefficientPolynomialMap (strictEGaloisCoefficientLift K σ) (U i j))

theorem strictEGaloisCommonClearing_ordinaryAtOne (T : Polynomial AlgebraicComplex)
    (hT : T.eval 1 ≠ 0) : (strictEGaloisCommonClearing K T).eval 1 ≠ 0 := by
  classical
  exact finiteBlockClearingPolynomial_ordinaryAtOne _
    (fun σ => coefficientMapped_ordinaryAtOne (strictEGaloisCoefficientLift K σ).toAlgHom.toRingHom T hT)

theorem strictEGaloisBlockCompanion_clearing {r : ℕ}
    (b : Fin r → RatFunc AlgebraicComplex) (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex))
    (hc : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (U i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T *
        minimalDerivativeCompanion r b i j) :
    ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex)
        (strictEGaloisClearedBlockMatrix K T U i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex)
        (strictEGaloisCommonClearing K T) * strictEGaloisBlockCompanion K r b i j := by
  classical
  apply finiteBlock_diagonal_clearing
  intro σ i j
  rw [← coefficientRatFuncHom_companion]
  exact coefficientMapped_clearing (strictEGaloisCoefficientLift K σ).toAlgHom.toRingHom
    (minimalDerivativeCompanion r b) T U hc i j

theorem strictEGaloisBlockFamily_independent (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (stage41_strictFormalSeries (fun n => (a n : AlgebraicComplex)))) r b)
    (σ : K ≃ₐ[ℚ] K) :
    LinearIndependent (RatFunc AlgebraicComplex) (fun i : Fin r =>
      (show LaurentSeries AlgebraicComplex from
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (strictEGaloisBlockFamily K a ha r (i, σ)))) := by
  exact actualConjugateDerivativePrefix_independent _ ha
    (strictEGaloisCoefficientLift K σ) r b hdata

theorem strictEGaloisBlockFamily_cleared (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (stage41_strictFormalSeries (fun n => (a n : AlgebraicComplex)))) r b)
    (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex))
    (hc : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (U i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T *
        minimalDerivativeCompanion r b i j) :
    ∀ i, Polynomial.aeval (subfieldEntireCoordinate (algebraicClosure ℚ ℂ).toSubfield)
        (show Polynomial (algebraicClosure ℚ ℂ).toSubfield from strictEGaloisCommonClearing K T) *
        subfieldEntireFunctionDerivation (algebraicClosure ℚ ℂ).toSubfield
          (strictEGaloisBlockFamily K a ha r i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate (algebraicClosure ℚ ℂ).toSubfield)
        (show Polynomial (algebraicClosure ℚ ℂ).toSubfield from strictEGaloisClearedBlockMatrix K T U i j) *
        strictEGaloisBlockFamily K a ha r j := by
  classical
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let F := fun (σ : K ≃ₐ[ℚ] K) =>
    actualConjugateDerivativePrefix (fun n => (a n : AlgebraicComplex)) ha
      (strictEGaloisCoefficientLift K σ) r
  let t : (K ≃ₐ[ℚ] K) → Polynomial k := fun σ =>
    show Polynomial k from algebraicCoefficientPolynomialMap (strictEGaloisCoefficientLift K σ) T
  let V : (K ≃ₐ[ℚ] K) → Matrix (Fin r) (Fin r) (Polynomial k) := fun σ i j =>
    show Polynomial k from algebraicCoefficientPolynomialMap (strictEGaloisCoefficientLift K σ) (U i j)
  have hs : ∀ σ i, Polynomial.aeval (subfieldEntireCoordinate k) (t σ) *
      subfieldEntireFunctionDerivation k (F σ i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (V σ i j) * F σ j := by
    intro σ i
    exact actualConjugateDerivativePrefix_cleared _ ha
      (strictEGaloisCoefficientLift K σ) r b hdata T U hc i
  exact finiteBlock_actual_cleared k F t V hs

/-- The zeroth coordinate of each literal block is the corresponding norm
factor, using only the restriction compatibility of the selected lift. -/
theorem strictEGaloisBlockFamily_zeroth (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (hr : 0 < r) (σ : K ≃ₐ[ℚ] K) (z : ℂ) :
    (strictEGaloisBlockFamily K a ha r (⟨0, hr⟩, σ)).val.val z =
      stage41_strictSeriesFunction (fun n => (σ (a n) : AlgebraicComplex)) z := by
  change stage41_strictSeriesFunction
    (fun n => (strictEGaloisCoefficientLift K σ) (a n : AlgebraicComplex)) z = _
  have heq : (fun n => (strictEGaloisCoefficientLift K σ) (a n : AlgebraicComplex)) =
      (fun n => (σ (a n) : AlgebraicComplex)) := by
    funext n
    exact strictEGaloisCoefficientLift_commutes K σ (a n)
  rw [heq]

theorem strictEGaloisBlockFamily_identity_factor (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (hr : 0 < r) (f : ℂ → ℂ)
    (hs : ∀ z : ℂ, HasSum
      (fun n => ((a n : AlgebraicComplex) : ℂ) * z^n / (n.factorial : ℂ)) (f z)) :
    (strictEGaloisBlockFamily K a ha r (⟨0, hr⟩, 1)).val.val = f := by
  funext z
  rw [strictEGaloisBlockFamily_zeroth]
  change stage41_strictSeriesFunction (fun n => (a n : AlgebraicComplex)) z = f z
  exact congrFun (stage41_strictSeriesFunction_eq_of_representation ha f hs) z

theorem strictEGaloisBlockFamily_product (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (hr : 0 < r) (z : ℂ) :
    (∏ σ : K ≃ₐ[ℚ] K, (strictEGaloisBlockFamily K a ha r (⟨0, hr⟩, σ)).val.val z) =
      strictEGaloisNormFunction K a z := by
  unfold strictEGaloisNormFunction
  apply Finset.prod_congr rfl
  intro σ _
  exact strictEGaloisBlockFamily_zeroth K a ha r hr σ z

/-- The exact polynomial used in the norm-quotient construction. -/
def strictEGaloisNormPolynomial (r : ℕ) (hr : 0 < r) :
    MvPolynomial (Fin r × (K ≃ₐ[ℚ] K)) (RatFunc AlgebraicComplex) :=
  ∏ σ : K ≃ₐ[ℚ] K, MvPolynomial.X (⟨0, hr⟩, σ)

theorem strictEGaloisNormPolynomial_eval {R : Type*} [CommSemiring R]
    (φ : RatFunc AlgebraicComplex →+* R)
    (r : ℕ) (hr : 0 < r) (y : Fin r × (K ≃ₐ[ℚ] K) → R) :
    MvPolynomial.eval₂Hom φ y (strictEGaloisNormPolynomial K r hr) =
      ∏ σ : K ≃ₐ[ℚ] K, y (⟨0, hr⟩, σ) := by
  simp only [strictEGaloisNormPolynomial, map_prod, MvPolynomial.eval₂Hom_X']

/-- Functional polynomial evaluation is the Laurent image of the same actual
entire product. Numerical evaluation was established separately above. -/
theorem strictEGaloisNormPolynomial_actualLaurent (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (hr : 0 < r) :
    MvPolynomial.eval₂Hom (algebraMap (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex))
      (fun i => (show LaurentSeries AlgebraicComplex from
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (strictEGaloisBlockFamily K a ha r i)))
      (strictEGaloisNormPolynomial K r hr) =
    (show LaurentSeries AlgebraicComplex from
      stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (∏ σ : K ≃ₐ[ℚ] K, strictEGaloisBlockFamily K a ha r (⟨0, hr⟩, σ))) := by
  rw [strictEGaloisNormPolynomial_eval, map_prod]

end GaloisBlocks

/-! Reindexing to the Fin cardinal used by the ordinary gauge interface. -/
theorem reindexed_block_fiber_linearIndependent
    {R M I S J : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (e : (I × S) ≃ J) (f : I × S → M)
    (hli : ∀ s, LinearIndependent R (fun i : I => f (i, s))) (j : J) :
    LinearIndependent R
      (fun x : {x : J // (e.symm x).2 = (e.symm j).2} => f (e.symm x.val)) := by
  let p : {x : J // (e.symm x).2 = (e.symm j).2} → I := fun x => (e.symm x.val).1
  have hp : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    exact Prod.ext hxy (x.property.trans y.property.symm)
  have hfamily :
      (fun x : {x : J // (e.symm x).2 = (e.symm j).2} => f (e.symm x.val)) =
      (fun x => f (p x, (e.symm j).2)) := by
    funext x
    apply congrArg f
    exact Prod.ext rfl x.property
  rw [hfamily]
  exact (hli (e.symm j).2).comp p hp

theorem actualEntire_cleared_reindex
    {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (k : Subfield ℂ) (f : I → subfieldEntireFunctionAlgebra k)
    (T : Polynomial k) (U : Matrix I I (Polynomial k))
    (hs : ∀ i, Polynomial.aeval (subfieldEntireCoordinate k) T *
        subfieldEntireFunctionDerivation k (f i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (U i j) * f j) :
    ∀ i, Polynomial.aeval (subfieldEntireCoordinate k) T *
        subfieldEntireFunctionDerivation k (f (e.symm i)) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (U (e.symm i) (e.symm j)) *
        f (e.symm j) := by
  intro i
  rw [hs (e.symm i)]
  exact (e.symm.sum_comp (fun j =>
    Polynomial.aeval (subfieldEntireCoordinate k) (U (e.symm i) j) * f j)).symm

theorem blockDiagonal_reindex_offBlock
    {I S J R : Type*} [DecidableEq S] [Zero R]
    (e : (I × S) ≃ J) (A : S → Matrix I I R)
    (i j : J) (hij : (e.symm i).2 ≠ (e.symm j).2) :
    Matrix.blockDiagonal A (e.symm i) (e.symm j) = 0 := by
  simp only [Matrix.blockDiagonal_apply, if_neg hij]

end StrictEUnit
