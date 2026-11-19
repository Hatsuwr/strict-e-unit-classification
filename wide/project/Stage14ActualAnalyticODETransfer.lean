import Stage14LaurentPolynomialODEClosure
import StrictETaylorRealization

/-!
# Actual analytic polynomial ODE transfer

The actual entire functions with coefficients in a specified complex subfield
embed injectively and differentially into its Laurent-series field. Polynomial
ODE identities are transferred in both directions and evaluated back on every
complex point. This yields actual strict-E input ODE closure without assuming
an analytic realization or the desired closure theorem.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

local instance actualTransferEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))

/-- Actual subfield-valued Taylor expansion followed by the standard embedding
into Laurent series. -/
def stage14_subfieldEntireLaurentAlgHom (k : Subfield ℂ) :
    subfieldEntireFunctionAlgebra k →ₐ[k] LaurentSeries k :=
  { ((HahnSeries.ofPowerSeries ℤ k).comp (subfieldEntireTaylorAlgHom k).toRingHom) with
    commutes' := fun c => by
      change HahnSeries.ofPowerSeries ℤ k
        (subfieldEntireTaylorAlgHom k (algebraMap k (subfieldEntireFunctionAlgebra k) c)) = _
      rw [(subfieldEntireTaylorAlgHom k).commutes]
      rfl }

@[simp] theorem stage14_subfieldEntireLaurentAlgHom_apply (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    stage14_subfieldEntireLaurentAlgHom k f =
      HahnSeries.ofPowerSeries ℤ k (subfieldEntireTaylorAlgHom k f) := rfl

/-- Injectivity is inherited from actual entire Taylor reconstruction and the
standard power-to-Laurent-series embedding. -/
theorem stage14_subfieldEntireLaurentAlgHom_injective (k : Subfield ℂ) :
    Function.Injective (stage14_subfieldEntireLaurentAlgHom k) :=
  HahnSeries.ofPowerSeries_injective.comp (subfieldEntireTaylorAlgHom_injective k)

/-- The actual analytic derivative is carried to ordinary Laurent differentiation. -/
theorem stage14_subfieldEntireLaurentAlgHom_derivation (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    stage14_subfieldEntireLaurentAlgHom k (subfieldEntireFunctionDerivation k f) =
      laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k f) := by
  simp only [stage14_subfieldEntireLaurentAlgHom_apply,
    subfieldEntireTaylorAlgHom_derivation, laurentOrdinaryDerivation_ofPowerSeries]

/-- Differential compatibility for every derivative order. -/
theorem stage14_subfieldEntireLaurentAlgHom_iterate (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (n : ℕ) :
    stage14_subfieldEntireLaurentAlgHom k ((subfieldEntireFunctionDerivation k)^[n] f) =
      ((laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[n])
        (stage14_subfieldEntireLaurentAlgHom k f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      stage14_subfieldEntireLaurentAlgHom_derivation, ih]

/-- A polynomial in the actual analytic coordinate becomes that same polynomial
under the standard inclusion into Laurent series. -/
theorem stage14_subfieldEntireLaurentAlgHom_polynomial (k : Subfield ℂ)
    (p : Polynomial k) :
    stage14_subfieldEntireLaurentAlgHom k (Polynomial.aeval (subfieldEntireCoordinate k) p) =
      algebraMap (Polynomial k) (LaurentSeries k) p := by
  rw [stage14_subfieldEntireLaurentAlgHom_apply, ← Polynomial.aeval_algHom_apply,
    subfieldEntireTaylorAlgHom_coordinate, Polynomial.aeval_def,
    PowerSeries.algebraMap_eq, Polynomial.eval₂_C_X_eq_coe,
    Polynomial.algebraMap_hahnSeries_apply]

/-- Evaluation is of the actual entire function at an arbitrary complex point. -/
def stage14_subfieldEntireEvaluation (k : Subfield ℂ) (z : ℂ) :
    subfieldEntireFunctionAlgebra k →ₐ[k] ℂ where
  toFun f := f.val.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Polynomial evaluation agrees exactly with the original complex formula. -/
theorem stage14_subfieldEntireEvaluation_polynomial (k : Subfield ℂ) (z : ℂ)
    (p : Polynomial k) :
    stage14_subfieldEntireEvaluation k z (Polynomial.aeval (subfieldEntireCoordinate k) p) =
      p.eval₂ k.subtype z := by
  change stage14_subfieldEntireEvaluation k z
    (Polynomial.aeval (subfieldEntireCoordinate k) p) = Polynomial.aeval z p
  exact (Polynomial.aeval_algHom_apply (stage14_subfieldEntireEvaluation k z)
    (subfieldEntireCoordinate k) p).symm

/-- A nonzero polynomial-coefficient equation on actual complex functions,
with coefficients in the specified subfield. -/
def HasSubfieldPolynomialODE (k : Subfield ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ n : ℕ, ∃ p : Fin (n + 1) → Polynomial k,
    (∃ i, p i ≠ 0) ∧ ∀ z : ℂ,
      ∑ i, (p i).eval₂ k.subtype z * iteratedDeriv i.val f z = 0

/-- Polynomial identities in the actual entire algebra are exactly the
pointwise polynomial differential identities on the whole complex plane. -/
theorem stage14_actualPolynomialRelation_iff (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (n : ℕ) (p : Fin (n + 1) → Polynomial k) :
    (∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) *
      ((subfieldEntireFunctionDerivation k)^[i.val]) f = 0) ↔
    ∀ z : ℂ, ∑ i, (p i).eval₂ k.subtype z * iteratedDeriv i.val f.val.val z = 0 := by
  have heval (z : ℂ) :
      stage14_subfieldEntireEvaluation k z
        (∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) *
          ((subfieldEntireFunctionDerivation k)^[i.val]) f) =
      ∑ i, (p i).eval₂ k.subtype z * iteratedDeriv i.val f.val.val z := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, stage14_subfieldEntireEvaluation_polynomial]
    congr 1
    change (((subfieldEntireFunctionDerivation k)^[i.val]) f).val.val z = _
    rw [subfieldEntireFunctionDerivation_iterate]
  constructor
  · intro h z
    rw [← heval z, h, map_zero]
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change stage14_subfieldEntireEvaluation k z
      (∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) *
        ((subfieldEntireFunctionDerivation k)^[i.val]) f) = 0
    rw [heval z, h z]

/-- The actual nonzero analytic polynomial ODE is equivalent to the actual
Laurent-field polynomial ODE, with the very same coefficient tuple. -/
theorem stage14_actualODE_iff_laurentODE (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    HasSubfieldPolynomialODE k f.val.val ↔
      HasPolynomialScalarDifferentialRelation (k := k) (stage14_laurentAlgebraDerivation (k := k))
        (stage14_subfieldEntireLaurentAlgHom k f) := by
  have hsum (n : ℕ) (p : Fin (n + 1) → Polynomial k) :
      stage14_subfieldEntireLaurentAlgHom k
        (∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) *
          ((subfieldEntireFunctionDerivation k)^[i.val]) f) =
      ∑ i, (algebraMap (Polynomial k) (RatFunc k) (p i)) •
        ((laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val])
          (stage14_subfieldEntireLaurentAlgHom k f) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, stage14_subfieldEntireLaurentAlgHom_polynomial,
      stage14_subfieldEntireLaurentAlgHom_iterate, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)]
  constructor
  · rintro ⟨n, p, hp, heq⟩
    refine ⟨n, p, hp, ?_⟩
    change (∑ i, (algebraMap (Polynomial k) (RatFunc k) (p i)) •
      ((laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val])
        (stage14_subfieldEntireLaurentAlgHom k f)) = 0
    rw [← hsum]
    rw [(stage14_actualPolynomialRelation_iff k f n p).mpr heq, map_zero]
  · rintro ⟨n, p, hp, heq⟩
    change (∑ i, (algebraMap (Polynomial k) (RatFunc k) (p i)) •
      ((laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val])
        (stage14_subfieldEntireLaurentAlgHom k f)) = 0 at heq
    refine ⟨n, p, hp, (stage14_actualPolynomialRelation_iff k f n p).mp ?_⟩
    apply stage14_subfieldEntireLaurentAlgHom_injective k
    rw [map_zero, hsum, heq]

/-- Actual complex-function ODE closure under addition within the entire
subfield-Taylor algebra. -/
theorem stage14_actualSubfieldODE_add (k : Subfield ℂ)
    (f g : subfieldEntireFunctionAlgebra k)
    (hf : HasSubfieldPolynomialODE k f.val.val) (hg : HasSubfieldPolynomialODE k g.val.val) :
    HasSubfieldPolynomialODE k (fun z => f.val.val z + g.val.val z) := by
  change HasSubfieldPolynomialODE k (f + g).val.val
  apply (stage14_actualODE_iff_laurentODE k (f + g)).mpr
  have hmap : stage14_subfieldEntireLaurentAlgHom k (f + g) =
      stage14_subfieldEntireLaurentAlgHom k f + stage14_subfieldEntireLaurentAlgHom k g :=
    (stage14_subfieldEntireLaurentAlgHom k).map_add' f g
  rw [hmap]
  exact stage14_laurentPolynomialODE_add
    ((stage14_actualODE_iff_laurentODE k f).mp hf)
    ((stage14_actualODE_iff_laurentODE k g).mp hg)

/-- Actual complex-function ODE closure under multiplication within the entire
subfield-Taylor algebra. -/
theorem stage14_actualSubfieldODE_mul (k : Subfield ℂ)
    (f g : subfieldEntireFunctionAlgebra k)
    (hf : HasSubfieldPolynomialODE k f.val.val) (hg : HasSubfieldPolynomialODE k g.val.val) :
    HasSubfieldPolynomialODE k (fun z => f.val.val z * g.val.val z) := by
  change HasSubfieldPolynomialODE k (f * g).val.val
  apply (stage14_actualODE_iff_laurentODE k (f * g)).mpr
  rw [map_mul]
  exact stage14_laurentPolynomialODE_mul
    ((stage14_actualODE_iff_laurentODE k f).mp hf)
    ((stage14_actualODE_iff_laurentODE k g).mp hg)

/-- The subfield predicate specializes literally to the manuscript's actual
algebraic-polynomial ODE predicate. -/
theorem stage14_algebraicPolynomialODE_iff_subfield (f : ℂ → ℂ) :
    HasAlgebraicPolynomialODE f ↔
      HasSubfieldPolynomialODE (algebraicClosure ℚ ℂ).toSubfield f := Iff.rfl

/-- The actual sum of two strict E-functions satisfies a genuinely nonzero
algebraic-polynomial ODE, proved through its actual Taylor realization. -/
theorem strictEFunction_add_hasAlgebraicPolynomialODE {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g) :
    HasAlgebraicPolynomialODE (fun z => f z + g z) := by
  apply (stage14_algebraicPolynomialODE_iff_subfield _).mpr
  apply stage14_actualSubfieldODE_add (algebraicClosure ℚ ℂ).toSubfield
    (strictEFunctionTaylorRealization f hf) (strictEFunctionTaylorRealization g hg)
  · exact (stage14_algebraicPolynomialODE_iff_subfield f).mp hf.choose_spec.2.2.1
  · exact (stage14_algebraicPolynomialODE_iff_subfield g).mp hg.choose_spec.2.2.1

/-- The actual product of two strict E-functions satisfies a genuinely nonzero
algebraic-polynomial ODE. -/
theorem strictEFunction_mul_hasAlgebraicPolynomialODE {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g) :
    HasAlgebraicPolynomialODE (fun z => f z * g z) := by
  apply (stage14_algebraicPolynomialODE_iff_subfield _).mpr
  apply stage14_actualSubfieldODE_mul (algebraicClosure ℚ ℂ).toSubfield
    (strictEFunctionTaylorRealization f hf) (strictEFunctionTaylorRealization g hg)
  · exact (stage14_algebraicPolynomialODE_iff_subfield f).mp hf.choose_spec.2.2.1
  · exact (stage14_algebraicPolynomialODE_iff_subfield g).mp hg.choose_spec.2.2.1

end StrictEUnit
