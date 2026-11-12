import ActualLinearLiftingFromScalar
import OrdinaryRegularDenominatorClearing
import ActualStrictEConjugateBlocks
import ActualRationalProductQuotientOperator
import ActualBlockQuotientContradiction

/-! General scalar nonvanishing for the original actual strict-E predicate.
The original minimal data and local regularity produce a literal conjugate
block system. The same finite Galois coefficient product supplies the exact
quotient annihilator, and faithful independence is used within each block.
No minimal operator for the norm, joint block independence, or auxiliary
arithmetic hypothesis occurs in the final assertion. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
local instance generalNonvanishingCoefficientSemiring : Semiring AlgebraicComplex :=
  (inferInstance : Field AlgebraicComplex).toSemiring
attribute [local instance 2000] Algebra.toModule

local instance generalNonvanishingEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance generalNonvanishingEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

local instance generalNonvanishingEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

/-- Assemble the literal blocks over one finite Galois coefficient field.
All operator and independence information is derived from the displayed
minimal data for the same factorial-normalized coefficient sequence. -/
theorem strictE_nonvanishing_from_exact_galois_blocks
    (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K)
    (ha : HasStrictEArithmetic (fun n => (a n : AlgebraicComplex)))
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hfne : f ≠ 0)
    (hs : ∀ z : ℂ, HasSum
      (fun n => ((a n : AlgebraicComplex) : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (r : ℕ) (hr : 0 < r) (b : Fin r → RatFunc AlgebraicComplex)
    (hmin : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (stage41_strictFormalSeries (fun n => (a n : AlgebraicComplex)))) r b)
    (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex))
    (hT : T.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex)
        (U i j) = algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T *
          minimalDerivativeCompanion r b i j) : f 1 ≠ 0 := by
  classical
  intro hzero
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let I := Fin r × (K ≃ₐ[ℚ] K)
  let N := Fintype.card I
  let e : I ≃ Fin N := Fintype.equivFin I
  let F₀ : I → subfieldEntireFunctionAlgebra k := strictEGaloisBlockFamily K a ha r
  let A₀ : Matrix I I (RatFunc k) := strictEGaloisBlockCompanion K r b
  let t : Polynomial k := strictEGaloisCommonClearing K T
  let U₀ : Matrix I I (Polynomial k) := strictEGaloisClearedBlockMatrix K T U
  let F : Fin N → subfieldEntireFunctionAlgebra k := fun i => F₀ (e.symm i)
  let A : Matrix (Fin N) (Fin N) (RatFunc k) :=
    fun i j => A₀ (e.symm i) (e.symm j)
  let V : Matrix (Fin N) (Fin N) (Polynomial k) :=
    fun i j => U₀ (e.symm i) (e.symm j)
  let block : Fin N → (K ≃ₐ[ℚ] K) := fun i => (e.symm i).2
  let idx : (K ≃ₐ[ℚ] K) → Fin N := fun σ => e (⟨0, hr⟩, σ)

  have ht : t.eval 1 ≠ 0 := strictEGaloisCommonClearing_ordinaryAtOne K T hT
  have hV : ∀ i j, algebraMap (Polynomial k) (RatFunc k) (V i j) =
      algebraMap (Polynomial k) (RatFunc k) t * A i j := by
    intro i j
    exact strictEGaloisBlockCompanion_clearing K b T U hclear (e.symm i) (e.symm j)
  have hactual : ∀ i, Polynomial.aeval (subfieldEntireCoordinate k) t *
      subfieldEntireFunctionDerivation k (F i) =
        ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (V i j) * F j := by
    exact actualEntire_cleared_reindex e k F₀ t U₀
      (strictEGaloisBlockFamily_cleared K a ha r b hmin T U hclear)
  have hsystem : ∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (F i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        stage14_subfieldEntireLaurentAlgHom k (F j) :=
    actualEntire_cleared_system_to_laurent k F A t V ht hV hactual

  have hblock : ∀ i j, block i ≠ block j → A i j = 0 := by
    intro i j hij
    exact blockDiagonal_reindex_offBlock e
      (fun σ : K ≃ₐ[ℚ] K => minimalDerivativeCompanion r
        (fun u => coefficientRatFuncHom (strictEGaloisCoefficientLift K σ).toAlgHom.toRingHom (b u)))
      i j hij
  have hli : ∀ σ : K ≃ₐ[ℚ] K, LinearIndependent (RatFunc k)
      (fun j : {j // block j = block (idx σ)} =>
        stage14_subfieldEntireLaurentAlgHom k (F j.val)) := by
    intro σ
    exact reindexed_block_fiber_linearIndependent (R := RatFunc k) e
      (fun i => stage14_subfieldEntireLaurentAlgHom k (F₀ i))
      (fun τ => strictEGaloisBlockFamily_independent K a ha r b hmin τ) (idx σ)

  obtain ⟨hNorm, ⟨q, hq⟩, hNormNe, hNormZero⟩ :=
    actualStrictE_galoisNorm_properties K a hf hs
  let c : ℕ → AlgebraicComplex := fun n => algebraMap ℚ AlgebraicComplex (q n)
  have hc : ∀ n, ∃ u : ℚ, c n = algebraMap ℚ AlgebraicComplex u :=
    fun n => ⟨q n, rfl⟩
  have hcs : ∀ z : ℂ, HasSum
      (fun n => (c n : ℂ) * z ^ n / (n.factorial : ℂ)) (strictEGaloisNormFunction K a z) := by
    intro z
    simpa [c] using hq z
  have hprod : ∀ z : ℂ, (∏ σ : K ≃ₐ[ℚ] K, (F (idx σ)).val.val z) =
      strictEGaloisNormFunction K a z := by
    intro z
    dsimp only [F, idx]
    simp only [Equiv.symm_apply_apply]
    exact strictEGaloisBlockFamily_product K a ha r hr z
  obtain ⟨m, p, hord, hsource⟩ :=
    actual_rational_product_quotient_ordinary_annihilator F idx hNorm (hNormNe hfne)
      c hc hcs (hNormZero hzero) hprod
  exact actual_block_quotient_ordinary_annihilator_contradiction k F A hsystem t V ht hV
    block hblock idx hli m p hord hsource

/-- The original scalar assertion, with its original strict-E definition,
actual Taylor realization, chosen minimal data, and PowerSeries regularity.
Every coefficient field, conjugate block, denominator and operator is constructed. -/
theorem strictERegularMinimalNonvanishingAtOne : StrictERegularMinimalNonvanishingAtOne := by
  intro f hf hfne r hr b hmin hreg
  classical
  have hfcopy := hf
  obtain ⟨a, _hent, hs, _hode, _harith⟩ := hfcopy
  obtain ⟨T, hT, U, hU⟩ :=
    exists_ordinary_minimal_companion_clearing (1 : AlgebraicComplex) r b hreg
  obtain ⟨K, hK, hG, haK, _hTK, _hUK⟩ :=
    actualStrictE_same_coefficients_finiteGalois_clearing_field hf a hs T U
  letI : FiniteDimensional ℚ K := hK
  letI : IsGalois ℚ K := hG
  letI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  let aK : ℕ → K := fun n => ⟨a n, haK n⟩
  have hsK : ∀ z : ℂ, HasSum
      (fun n => ((aK n : AlgebraicComplex) : ℂ) * z ^ n / (n.factorial : ℂ)) (f z) := hs
  have ha : HasStrictEArithmetic (fun n => (aK n : AlgebraicComplex)) :=
    (stage41_actualStrictE_isStrictESeries hf _ hsK).1
  have htaylor := strictEFunctionTaylorRealization_eq_strictFormalSeries hf
    (fun n => (aK n : AlgebraicComplex)) hsK
  have hminK : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (stage41_strictFormalSeries (fun n => (aK n : AlgebraicComplex)))) r b := by
    simpa only [stage14_subfieldEntireLaurentAlgHom_apply, htaylor] using hmin
  exact strictE_nonvanishing_from_exact_galois_blocks K aK ha hf hfne hsK
    r hr b hminK T U hT hU

/-- Unconditional degree-one lifting for actual strict E-functions. -/
theorem strictELinearOrdinaryLiftingAtOne : StrictELinearOrdinaryLiftingAtOne :=
  strictELinearOrdinaryLifting_of_regularMinimalNonvanishing
    strictERegularMinimalNonvanishingAtOne

/-- Unconditional homogeneous lifting, preserving the exact specialized relation. -/
theorem strictEHomogeneousOrdinaryLiftingAtOne :
    HomogeneousOrdinaryLiftingAtOne IsStrictEFunction :=
  homogeneousOrdinaryLifting_of_regularMinimalNonvanishing
    strictERegularMinimalNonvanishingAtOne

/-- Unconditional exact Laurent relation lifting for the same strict-E predicate. -/
theorem strictELaurentRelationLifting : StrictELaurentRelationLifting :=
  strictELaurentLifting_of_regularMinimalNonvanishing
    strictERegularMinimalNonvanishingAtOne

end StrictEUnit
end
