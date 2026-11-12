import StrictECoefficientConjugation
import ActualStrictEMinimalCyclic
import MinimalCompanionPowerSeriesClearing
import Mathlib.Data.Matrix.Block

/-! Coefficient conjugation of the same actual derivative prefix.
The original minimal prefix is the only independence input. Each conjugate
prefix and its clearing are constructed from that input. No joint independence
of distinct conjugate blocks is asserted. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

variable {K L : Type*} [Field K] [Field L]

/-- Literal coefficientwise map, bundled to preserve products and finite sums. -/
def coefficientLaurentHom (φ : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun := fun x => x.map φ
  map_zero' := by ext n; simp [HahnSeries.map_coeff]
  map_one' := by
    ext n
    by_cases hn : n = 0 <;> simp [HahnSeries.map_coeff, HahnSeries.coeff_one, hn]
  map_add' x y := by ext n; simp [HahnSeries.map_coeff, HahnSeries.coeff_add]
  map_mul' x y := HahnSeries.map_mul φ.toNonUnitalRingHom

@[simp] theorem coefficientLaurentHom_coeff (φ : K →+* L)
    (x : LaurentSeries K) (n : ℤ) :
    (coefficientLaurentHom φ x).coeff n = φ (x.coeff n) := rfl

/-- Localization of the literal polynomial coefficient map. -/
def coefficientRatFuncHom (φ : K →+* L) : RatFunc K →+* RatFunc L :=
  let ψ := (algebraMap (Polynomial L) (RatFunc L)).comp (Polynomial.mapRingHom φ)
  RatFunc.liftRingHom ψ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ψ
      ((RatFunc.algebraMap_injective L).comp (Polynomial.map_injective φ φ.injective)))

@[simp] theorem coefficientRatFuncHom_polynomial (φ : K →+* L)
    (p : Polynomial K) :
    coefficientRatFuncHom φ (algebraMap (Polynomial K) (RatFunc K) p) =
      algebraMap (Polynomial L) (RatFunc L) (p.map φ) := by
  let ψ := (algebraMap (Polynomial L) (RatFunc L)).comp (Polynomial.mapRingHom φ)
  change RatFunc.liftRingHom ψ _ (algebraMap (Polynomial K) (RatFunc K) p) = ψ p
  simpa only [map_one, div_one] using
    (RatFunc.liftRingHom_apply_div ψ
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ψ
        ((RatFunc.algebraMap_injective L).comp (Polynomial.map_injective φ φ.injective))) p 1)

@[simp] theorem coefficientLaurentHom_ofPowerSeries (φ : K →+* L)
    (f : PowerSeries K) :
    coefficientLaurentHom φ (HahnSeries.ofPowerSeries ℤ K f) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map φ f) := by
  ext n
  rw [coefficientLaurentHom_coeff]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [powerSeries_laurent_coeff_neg _ n (lt_of_not_ge hn),
      powerSeries_laurent_coeff_neg _ n (lt_of_not_ge hn), map_zero]

@[simp] theorem coefficientLaurentHom_polynomial (φ : K →+* L)
    (p : Polynomial K) :
    coefficientLaurentHom φ (algebraMap (Polynomial K) (LaurentSeries K) p) =
      algebraMap (Polynomial L) (LaurentSeries L) (p.map φ) := by
  rw [Polynomial.algebraMap_hahnSeries_apply, coefficientLaurentHom_ofPowerSeries,
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.polynomial_map_coe]

@[simp] theorem coefficientLaurentHom_rational (φ : K →+* L) (q : RatFunc K) :
    coefficientLaurentHom φ (algebraMap (RatFunc K) (LaurentSeries K) q) =
      algebraMap (RatFunc L) (LaurentSeries L) (coefficientRatFuncHom φ q) := by
  induction q using RatFunc.induction_on
  rename_i p q hq
  simp only [map_div₀, coefficientRatFuncHom_polynomial,
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K),
    ← IsScalarTower.algebraMap_apply (Polynomial L) (RatFunc L) (LaurentSeries L),
    coefficientLaurentHom_polynomial]

@[simp] theorem coefficientLaurentHom_smul (φ : K →+* L)
    (q : RatFunc K) (x : LaurentSeries K) :
    coefficientLaurentHom φ (q • x) =
      coefficientRatFuncHom φ q • coefficientLaurentHom φ x := by
  simp only [Algebra.smul_def, map_mul, coefficientLaurentHom_rational]

@[simp] theorem coefficientLaurentHom_inverse (σ : K ≃+* L) (x : LaurentSeries K) :
    coefficientLaurentHom σ.symm.toRingHom (coefficientLaurentHom σ.toRingHom x) = x := by
  ext n
  change σ.symm (σ (x.coeff n)) = x.coeff n
  exact σ.symm_apply_apply (x.coeff n)

@[simp] theorem coefficientLaurentHom_derivative (φ : K →+* L) (x : LaurentSeries K) :
    coefficientLaurentHom φ (laurentOrdinaryDerivation x) =
      laurentOrdinaryDerivation (coefficientLaurentHom φ x) := by
  ext n
  simp only [coefficientLaurentHom_coeff, laurentOrdinaryDerivation_coeff,
    map_mul, map_intCast]

theorem coefficientLaurentHom_iterate_derivative (φ : K →+* L)
    (x : LaurentSeries K) (n : ℕ) :
    coefficientLaurentHom φ
        ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[n] x) =
      (laurentOrdinaryDerivation : LaurentSeries L → LaurentSeries L)^[n]
        (coefficientLaurentHom φ x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', coefficientLaurentHom_derivative,
      ih, Function.iterate_succ_apply']

/-- Pull a hypothetical conjugate relation back through the inverse coefficient
map. The RatFunc coefficient map is injective because its domain is a field. -/
theorem coefficientConjugate_linearIndependent {ι : Type*} [Fintype ι]
    (σ : K ≃+* L) (f : ι → LaurentSeries K)
    (hli : LinearIndependent (RatFunc K) f) :
    LinearIndependent (RatFunc L) (fun i => coefficientLaurentHom σ.toRingHom (f i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hpull := congrArg (coefficientLaurentHom σ.symm.toRingHom) hc
  simp only [map_sum, coefficientLaurentHom_smul,
    coefficientLaurentHom_inverse, map_zero] at hpull
  have hz := Fintype.linearIndependent_iff.mp hli _ hpull i
  apply (coefficientRatFuncHom σ.symm.toRingHom).injective
  simpa only [map_zero] using hz

/-- In particular the same derivative orders remain independent. -/
theorem coefficientConjugate_derivativePrefix_linearIndependent
    (σ : K ≃+* L) (G : PowerSeries K) (r : ℕ)
    (hli : LinearIndependent (RatFunc K) (fun i : Fin r =>
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (HahnSeries.ofPowerSeries ℤ K G))) :
    LinearIndependent (RatFunc L) (fun i : Fin r =>
      HahnSeries.ofPowerSeries ℤ L
        (ordinaryDerivativePrefix r (PowerSeries.map σ.toRingHom G) i)) := by
  have h := coefficientConjugate_linearIndependent σ _ hli
  simpa only [coefficientLaurentHom_iterate_derivative,
    coefficientLaurentHom_ofPowerSeries,
    laurentOrdinaryDerivation_iterate_ofPowerSeries, ordinaryDerivativePrefix,
    ordinaryBorel_map_iterate_derivative] using h

/-- Mapped coefficients are the literal companion of the mapped recurrence. -/
theorem coefficientRatFuncHom_companion (φ : K →+* L)
    (r : ℕ) (b : Fin r → RatFunc K) (i j : Fin r) :
    coefficientRatFuncHom φ (minimalDerivativeCompanion r b i j) =
      minimalDerivativeCompanion r (fun j => coefficientRatFuncHom φ (b j)) i j := by
  simp only [minimalDerivativeCompanion]
  split_ifs <;> simp

theorem coefficientMapped_clearing {r : ℕ} (φ : K →+* L)
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * A i j) :
    ∀ i j, algebraMap (Polynomial L) (RatFunc L) ((U i j).map φ) =
      algebraMap (Polynomial L) (RatFunc L) (T.map φ) * coefficientRatFuncHom φ (A i j) := by
  intro i j
  simpa only [map_mul, coefficientRatFuncHom_polynomial] using
    congrArg (coefficientRatFuncHom φ) (hclear i j)

theorem coefficientMapped_ordinaryAtOne (φ : K →+* L) (T : Polynomial K)
    (hT : T.eval 1 ≠ 0) : (T.map φ).eval 1 ≠ 0 := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_one]
  exact (map_ne_zero φ).mpr hT

theorem coefficientMapped_powerSeries_cleared {ι : Type*} [Fintype ι]
    (φ : K →+* L) (f : ι → PowerSeries K) (T : Polynomial K)
    (U : Matrix ι ι (Polynomial K))
    (hs : ∀ i, (T : PowerSeries K) * PowerSeries.derivative K (f i) =
      ∑ j, (U i j : PowerSeries K) * f j) :
    ∀ i, (T.map φ : PowerSeries L) * PowerSeries.derivative L (PowerSeries.map φ (f i)) =
      ∑ j, ((U i j).map φ : PowerSeries L) * PowerSeries.map φ (f j) := by
  intro i
  have h := congrArg (PowerSeries.map φ) (hs i)
  simpa only [map_mul, map_sum, ordinaryBorel_map_derivative,
    ← Polynomial.polynomial_map_coe] using h

/-! Actual source adapter. -/
attribute [local instance 2000] Algebra.toModule

local instance conjugatePrefixEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance conjugatePrefixEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

local instance conjugatePrefixEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

/-- Derivatives of the actual function reconstructed from the conjugate
factorial coefficients, rather than arbitrary solutions of a conjugate ODE. -/
def actualConjugateDerivativePrefix (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a)
    (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (r : ℕ) :
    Fin r → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
  fun i => (subfieldEntireFunctionDerivation (algebraicClosure ℚ ℂ).toSubfield)^[i.val]
    (stage41_strictSeriesRealization (fun n => σ (a n))
      (strictEArithmetic_map σ.toAlgHom ha))

theorem actualConjugateDerivativePrefix_taylor (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a)
    (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (r : ℕ) (i : Fin r) :
    subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (actualConjugateDerivativePrefix a ha σ r i) =
      ordinaryDerivativePrefix r
        (PowerSeries.map σ.toRingHom (stage41_strictFormalSeries a)) i := by
  unfold actualConjugateDerivativePrefix ordinaryDerivativePrefix
  rw [stage26_subfieldTaylor_iterate, stage41_strictSeries_taylor,
    stage41_strictFormalSeries_map]
  rfl

theorem actualConjugateDerivativePrefix_laurent (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a)
    (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (r : ℕ) (i : Fin r) :
    stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (actualConjugateDerivativePrefix a ha σ r i) =
      coefficientLaurentHom σ.toRingHom
        ((laurentOrdinaryDerivation : LaurentSeries AlgebraicComplex →
          LaurentSeries AlgebraicComplex)^[i.val]
            (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a))) := by
  rw [stage14_subfieldEntireLaurentAlgHom_apply,
    actualConjugateDerivativePrefix_taylor,
    coefficientLaurentHom_iterate_derivative, coefficientLaurentHom_ofPowerSeries,
    laurentOrdinaryDerivation_iterate_ofPowerSeries]
  rfl

/-- The only independence premise is the original function's exact minimal data. -/
theorem actualConjugateDerivativePrefix_independent (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a)
    (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b) :
    LinearIndependent (RatFunc AlgebraicComplex) (fun i =>
      (show LaurentSeries AlgebraicComplex from
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (actualConjugateDerivativePrefix a ha σ r i))) := by
  simpa only [actualConjugateDerivativePrefix_laurent] using
    coefficientConjugate_linearIndependent σ.toRingEquiv _ hdata.1

/-- Reflect the mapped formal equation through the injective actual Taylor map. -/
theorem actualConjugateDerivativePrefix_cleared (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a)
    (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b)
    (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex))
    (hclear : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (U i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T *
        minimalDerivativeCompanion r b i j) :
    ∀ i, Polynomial.aeval (subfieldEntireCoordinate (algebraicClosure ℚ ℂ).toSubfield)
        (show Polynomial (algebraicClosure ℚ ℂ).toSubfield from T.map σ.toRingHom) *
        subfieldEntireFunctionDerivation (algebraicClosure ℚ ℂ).toSubfield
          (actualConjugateDerivativePrefix a ha σ r i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate (algebraicClosure ℚ ℂ).toSubfield)
        (show Polynomial (algebraicClosure ℚ ℂ).toSubfield from (U i j).map σ.toRingHom) *
        actualConjugateDerivativePrefix a ha σ r j := by
  have hs := (minimal_companion_powerSeries_clearing
    (stage41_strictFormalSeries a) r b hdata T U hclear).2
  have hm := coefficientMapped_powerSeries_cleared σ.toRingHom
    (ordinaryDerivativePrefix r (stage41_strictFormalSeries a)) T U hs
  intro i
  apply subfieldEntireTaylorAlgHom_injective (algebraicClosure ℚ ℂ).toSubfield
  simp only [map_mul, map_sum, stage26_subfieldTaylor_polynomial,
    subfieldEntireTaylorAlgHom_derivation, actualConjugateDerivativePrefix_taylor]
  simpa only [ordinaryDerivativePrefix, ordinaryBorel_map_iterate_derivative] using hm i

/-! A single ordinary clearing for any finite family of the mapped blocks. -/
section CommonClearing
variable {S : Type*} [Fintype S] [DecidableEq S]

def finiteBlockClearingPolynomial (T : S → Polynomial K) : Polynomial K := ∏ s, T s

def finiteBlockClearingMultiplier (T : S → Polynomial K) (s : S) : Polynomial K :=
  ∏ u ∈ (Finset.univ : Finset S).erase s, T u

theorem finiteBlockClearingMultiplier_mul (T : S → Polynomial K) (s : S) :
    finiteBlockClearingMultiplier T s * T s = finiteBlockClearingPolynomial T :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ s)

theorem finiteBlockClearingPolynomial_ordinaryAtOne (T : S → Polynomial K)
    (hT : ∀ s, (T s).eval 1 ≠ 0) : (finiteBlockClearingPolynomial T).eval 1 ≠ 0 := by
  unfold finiteBlockClearingPolynomial
  rw [Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun s _ => hT s)

/-- Multiplying each mapped clearing by the product of all other denominators
retains that block's exact rational matrix. -/
theorem finiteBlock_common_clearing {r : ℕ}
    (A : S → Matrix (Fin r) (Fin r) (RatFunc K))
    (T : S → Polynomial K) (U : S → Matrix (Fin r) (Fin r) (Polynomial K))
    (hc : ∀ s i j, algebraMap (Polynomial K) (RatFunc K) (U s i j) =
      algebraMap (Polynomial K) (RatFunc K) (T s) * A s i j) :
    ∀ s i j, algebraMap (Polynomial K) (RatFunc K)
        (finiteBlockClearingMultiplier T s * U s i j) =
      algebraMap (Polynomial K) (RatFunc K) (finiteBlockClearingPolynomial T) * A s i j := by
  intro s i j
  rw [map_mul, hc, ← mul_assoc, ← map_mul, finiteBlockClearingMultiplier_mul]

/-- Literal block diagonal assembly, with the derivative index first. -/
theorem finiteBlock_diagonal_clearing {r : ℕ}
    (A : S → Matrix (Fin r) (Fin r) (RatFunc K))
    (T : S → Polynomial K) (U : S → Matrix (Fin r) (Fin r) (Polynomial K))
    (hc : ∀ s i j, algebraMap (Polynomial K) (RatFunc K) (U s i j) =
      algebraMap (Polynomial K) (RatFunc K) (T s) * A s i j) :
    ∀ i j : Fin r × S, algebraMap (Polynomial K) (RatFunc K)
        (Matrix.blockDiagonal (fun s i j => finiteBlockClearingMultiplier T s * U s i j) i j) =
      algebraMap (Polynomial K) (RatFunc K) (finiteBlockClearingPolynomial T) *
        Matrix.blockDiagonal A i j := by
  intro i j
  simp only [Matrix.blockDiagonal_apply]
  split_ifs with h
  · exact finiteBlock_common_clearing A T U hc i.2 i.1 j.1
  · simp

end CommonClearing
end StrictEUnit
