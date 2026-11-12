import Stage14ActualAnalyticODETransfer

/-! NEW PROOF RECONSTRUCTION, not recovered historical source.
Dividing an entire algebraic-Taylor function by a nonzero polynomial, when
the quotient is entire with algebraic Taylor coefficients, preserves a
nonzero polynomial-coefficient differential equation. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

/-- Rational scalar multiples stay in the same finite differential span. -/
theorem division_laurentPolynomialODE_rat_smul {k : Type*} [Field k]
    (b : RatFunc k) {f : LaurentSeries k}
    (hf : HasPolynomialScalarDifferentialRelation (k := k)
      (stage14_laurentAlgebraDerivation (k := k)) f) :
    HasPolynomialScalarDifferentialRelation (k := k)
      (stage14_laurentAlgebraDerivation (k := k)) (b • f) := by
  letI : SMul k (LaurentSeries k) := Algebra.toSMul
  letI : SMul k (RatFunc k) := Algebra.toSMul
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : Module k (RatFunc k) := Algebra.toModule
  letI : IsScalarTower k (RatFunc k) (LaurentSeries k) := stage14_rationalLaurentScalarTower
  apply finiteDifferentialSpan_polynomialScalarRelation
  obtain ⟨M, hfg, hstable, hmem⟩ := scalarLinearDifferentialRelation_finiteSpan
    (stage14_rationalOrdinaryDerivation (k := k))
    (stage14_laurentAlgebraDerivation (k := k))
    (fun c => stage14_rationalLaurent_differential (k := k) c)
    ((stage14_polynomialScalarRelation_iff _ f).mp hf)
  exact ⟨M, hfg, hstable, M.smul_mem b hmem⟩

/-- The literal polynomial product equation survives the actual Taylor and
Laurent embeddings. -/
theorem division_actual_polynomial_mul_laurent (k : Subfield ℂ)
    (F G : subfieldEntireFunctionAlgebra k) (P : Polynomial k)
    (hmul : ∀ z, P.eval₂ k.subtype z * G.val.val z = F.val.val z) :
    algebraMap (Polynomial k) (LaurentSeries k) P *
      stage14_subfieldEntireLaurentAlgHom k G =
      stage14_subfieldEntireLaurentAlgHom k F := by
  have he : Polynomial.aeval (subfieldEntireCoordinate k) P * G = F := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change stage14_subfieldEntireEvaluation k z
      (Polynomial.aeval (subfieldEntireCoordinate k) P * G) = F.val.val z
    rw [map_mul, stage14_subfieldEntireEvaluation_polynomial]
    exact hmul z
  have hm := congrArg (stage14_subfieldEntireLaurentAlgHom k) he
  simpa only [map_mul, stage14_subfieldEntireLaurentAlgHom_polynomial] using hm

/-- No nonzero ODE is hypothesized for the quotient: it is constructed from
its rational scalar membership in the original finite differential span. -/
theorem division_actualSubfieldODE_of_polynomial_mul (k : Subfield ℂ)
    (F G : subfieldEntireFunctionAlgebra k) (P : Polynomial k) (hP : P ≠ 0)
    (hF : HasSubfieldPolynomialODE k F.val.val)
    (hmul : ∀ z, P.eval₂ k.subtype z * G.val.val z = F.val.val z) :
    HasSubfieldPolynomialODE k G.val.val := by
  apply (stage14_actualODE_iff_laurentODE k G).mpr
  let p : RatFunc k := algebraMap (Polynomial k) (RatFunc k) P
  have hp : p ≠ 0 := by
    exact fun h => hP (IsFractionRing.to_map_eq_zero_iff.mp h)
  have hpL : algebraMap (RatFunc k) (LaurentSeries k) p ≠ 0 := by
    exact (map_ne_zero (algebraMap (RatFunc k) (LaurentSeries k))).mpr hp
  have hmulL := division_actual_polynomial_mul_laurent k F G P hmul
  have heq : stage14_subfieldEntireLaurentAlgHom k G =
      p⁻¹ • stage14_subfieldEntireLaurentAlgHom k F := by
    rw [Algebra.smul_def, map_inv₀, ← hmulL]
    have hmap : algebraMap (Polynomial k) (LaurentSeries k) P =
        algebraMap (RatFunc k) (LaurentSeries k) p :=
      IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k) P
    rw [hmap, ← mul_assoc, inv_mul_cancel₀ hpL, one_mul]
  rw [heq]
  exact division_laurentPolynomialODE_rat_smul p⁻¹
    ((stage14_actualODE_iff_laurentODE k F).mp hF)

end StrictEUnit
