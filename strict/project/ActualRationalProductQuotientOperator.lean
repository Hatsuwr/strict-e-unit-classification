import UniversalQuotientAnnihilator
import OrdinaryScaledProductInitialZero

/-! An actual rational strict-E product vanishing at one supplies the exact
ordinary quotient annihilator required by the universal ideal argument. The
finite actual family, its literal product, and its canonical Laurent embedding
are retained. Neither minimal data nor an annihilator premise is supplied. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
attribute [local instance 2000] Algebra.toModule

local instance actualProductEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance actualProductEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

local instance actualProductEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ (@NonUnitalNonAssocSemiring.toMulZeroClass _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring)))

/-- Pointwise equality of the actual finite product gives equality of the
literal Laurent products, by function extensionality and the actual ring map. -/
theorem actual_entire_product_laurent_same_source
    (k : Subfield ℂ) {ι S : Type*} [Fintype S]
    (f : ι → subfieldEntireFunctionAlgebra k) (idx : S → ι)
    (F : subfieldEntireFunctionAlgebra k)
    (hprod : ∀ z : ℂ, (∏ s, (f (idx s)).val.val z) = F.val.val z) :
    (∏ s, stage14_subfieldEntireLaurentAlgHom k (f (idx s))) =
      stage14_subfieldEntireLaurentAlgHom k F := by
  classical
  have he : (∏ s, f (idx s)) = F := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change stage14_subfieldEntireEvaluation k z (∏ s, f (idx s)) = F.val.val z
    rw [map_prod]
    exact hprod z
  have hm := congrArg (stage14_subfieldEntireLaurentAlgHom k) he
  simpa only [map_prod] using hm

/-- Cancellation is proved over an abstract coefficient field, so every
Laurent operation uses one fixed field instance. -/
private theorem actualProduct_inverseLinear_cancel
    {K : Type*} [Field K] (F G : LaurentSeries K)
    (hmul : algebraMap (Polynomial K) (LaurentSeries K)
      (Polynomial.X - Polynomial.C (1 : K)) * G = F) :
    algebraMap (RatFunc K) (LaurentSeries K)
      (ordinaryPointInverseLinear (1 : K)) * F = G := by
  have hPL : algebraMap (Polynomial K) (LaurentSeries K)
      (Polynomial.X - Polynomial.C (1 : K)) ≠ 0 := by
    simpa only [map_zero] using
      (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).ne
        (Polynomial.X_sub_C_ne_zero (1 : K))
  dsimp only [ordinaryPointInverseLinear]
  rw [map_inv₀, ← IsScalarTower.algebraMap_apply
    (Polynomial K) (RatFunc K) (LaurentSeries K),
    ← hmul, ← mul_assoc, inv_mul_cancel₀ hPL, one_mul]

/-- The same actual quotient equation and operator transfer to the literal
scaled product over any one fixed complex coefficient subfield. -/
private theorem actualProduct_quotient_operator_transfer
    (k : Subfield ℂ) {ι S : Type*} [Fintype S]
    (f : ι → subfieldEntireFunctionAlgebra k) (idx : S → ι)
    (F G : subfieldEntireFunctionAlgebra k)
    (hprod : ∀ z : ℂ, (∏ s, (f (idx s)).val.val z) = F.val.val z)
    (hmul : ∀ z : ℂ, (z - 1) * G.val.val z = F.val.val z)
    (m : ℕ) (p : Fin (m+1) → Polynomial k)
    (hode : ∀ z : ℂ, ∑ i, (p i).eval₂ k.subtype z *
      iteratedDeriv i.val G.val.val z = 0) :
    (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (algebraMap (RatFunc k) (LaurentSeries k)
          (ordinaryPointInverseLinear (1 : k)) *
          ∏ s, stage14_subfieldEntireLaurentAlgHom k (f (idx s)))) = 0 := by
  classical
  have hprodL := actual_entire_product_laurent_same_source k f idx F hprod
  have hmulL := actual_polynomial_mul_laurent_same_source k F G
    (Polynomial.X - Polynomial.C (1 : k))
    (by intro z; simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_one, map_one] using hmul z)
  have hquot := actualProduct_inverseLinear_cancel
    (stage14_subfieldEntireLaurentAlgHom k F)
    (stage14_subfieldEntireLaurentAlgHom k G) hmulL
  rw [hprodL, hquot]
  exact actual_polynomial_relation_laurent_same_tuple k G m p hode

-- This is the same underlying subtype as AlgebraicComplex. Fix its
-- Subfield spelling for all Laurent operations, matching the actual embedding.

/-- Rational factorial coefficients of the actual product yield an actual
strict-E quotient. Its constructed ordinary operator is transferred to the
same scaled Laurent product, rather than replaced by any factor's operator. -/
theorem actual_rational_product_quotient_ordinary_annihilator
    {ι S : Type*} [Fintype S]
    (f : ι → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (idx : S → ι) {H : ℂ → ℂ} (hH : IsStrictEFunction H)
    (hHne : H ≠ (fun _ => 0))
    (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : ∀ z : ℂ, HasSum
      (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (H z))
    (hzero : H 1 = 0)
    (hprod : ∀ z : ℂ, (∏ s, (f (idx s)).val.val z) = H z) :
    ∃ m : ℕ, ∃ p : Fin (m+1) → Polynomial AlgebraicComplex,
      (p (Fin.last m)).eval 1 ≠ 0 ∧
      (∑ i, algebraMap (Polynomial ((algebraicClosure ℚ ℂ).toSubfield))
          (LaurentSeries ((algebraicClosure ℚ ℂ).toSubfield)) (p i) *
        (laurentOrdinaryDerivation : LaurentSeries ((algebraicClosure ℚ ℂ).toSubfield) →
          LaurentSeries ((algebraicClosure ℚ ℂ).toSubfield))^[i.val]
          (algebraMap (RatFunc ((algebraicClosure ℚ ℂ).toSubfield)) (LaurentSeries ((algebraicClosure ℚ ℂ).toSubfield))
            (ordinaryPointInverseLinear (1 : ((algebraicClosure ℚ ℂ).toSubfield))) *
            ∏ s, stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
              (f (idx s)))) = 0 := by
  classical
  obtain ⟨g, hg, hmul, m, p, hord, hode⟩ :=
    rational_actualStrictE_division_ordinary_annihilator hH hHne a hrat hs hzero
  refine ⟨m, p, hord, ?_⟩
  exact actualProduct_quotient_operator_transfer
    (algebraicClosure ℚ ℂ).toSubfield f idx
    (strictEFunctionTaylorRealization H hH)
    (strictEFunctionTaylorRealization g hg) hprod hmul m p hode

end StrictEUnit
end
