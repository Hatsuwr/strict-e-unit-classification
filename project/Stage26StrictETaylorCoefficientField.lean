import Stage26FiniteCoefficientField
import Stage14ActualAnalyticODETransfer

/-!
# Genuine strict-E coefficients and their Taylor coefficient field

The analytic/Taylor and derivative transports used below are already proved
in Stage14. This module records their power-series ODE consequence and the
fact that factorial normalization does not change coefficient-field membership.
It does not yet assert that the scalar ODE supplies a finite coefficient field.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

/-- Every coefficient of the actual algebraic Taylor realization is the
factorial-normalized coefficient of any supplied actual strict-E series. -/
theorem stage26_strictE_taylor_coefficient {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (a : ℕ → AlgebraicComplex)
    (ha : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (n : ℕ) :
    PowerSeries.coeff AlgebraicComplex n
      (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization f hf)) = a n / (n.factorial : AlgebraicComplex) := by
  apply Subtype.ext
  have h : entireCauchyCoefficient f n = (a n : ℂ) / (n.factorial : ℂ) := by
    apply entireCauchyCoefficient_eq_of_hasSum (strictEFunction_differentiable hf)
    intro z
    convert ha z using 1
    funext j
    ring
  simpa [subfieldEntireTaylorAlgHom, subfieldEntireTaylorSeries] using h

/-- Dividing an algebraic sequence by rational factorials preserves its exact
membership in every intermediate coefficient field. -/
theorem stage26_factorial_normalization_mem_iff
    (F : IntermediateField ℚ AlgebraicComplex) (a : ℕ → AlgebraicComplex) (n : ℕ) :
    a n / (n.factorial : AlgebraicComplex) ∈ F ↔ a n ∈ F := by
  constructor
  · intro h
    have hm := F.mul_mem h (F.natCast_mem n.factorial)
    have hn : (n.factorial : AlgebraicComplex) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simpa only [div_mul_cancel₀ _ hn] using hm
  · intro h
    exact F.div_mem h (F.natCast_mem n.factorial)

/-- In particular, any finite field containing the genuine ordinary Taylor
coefficients contains every coefficient in the defining strict-E sequence. -/
theorem stage26_strictE_coefficient_field_of_taylor {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (F : IntermediateField ℚ AlgebraicComplex)
    (hF : ∀ n, PowerSeries.coeff AlgebraicComplex n
      (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization f hf)) ∈ F)
    (a : ℕ → AlgebraicComplex)
    (ha : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) :
    ∀ n, a n ∈ F := by
  intro n
  apply (stage26_factorial_normalization_mem_iff F a n).mp
  rw [← stage26_strictE_taylor_coefficient hf a ha n]
  exact hF n

/-- The already-proved actual Taylor derivative transport iterates. -/
theorem stage26_subfieldTaylor_iterate (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (n : ℕ) :
    subfieldEntireTaylorAlgHom k ((subfieldEntireFunctionDerivation k)^[n] f) =
      (PowerSeries.derivative k : PowerSeries k → PowerSeries k)^[n]
        (subfieldEntireTaylorAlgHom k f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      subfieldEntireTaylorAlgHom_derivation, ih]

/-- Polynomial coordinates are transported by the already-constructed genuine
Taylor algebra homomorphism. -/
theorem stage26_subfieldTaylor_polynomial (k : Subfield ℂ) (p : Polynomial k) :
    subfieldEntireTaylorAlgHom k (Polynomial.aeval (subfieldEntireCoordinate k) p) =
      (p : PowerSeries k) := by
  rw [← Polynomial.aeval_algHom_apply, subfieldEntireTaylorAlgHom_coordinate,
    Polynomial.aeval_def, PowerSeries.algebraMap_eq, Polynomial.eval₂_C_X_eq_coe]

/-- The actual analytic polynomial ODE yields the identical nonzero tuple
of polynomial coefficients in the actual algebraic Taylor-series ODE. -/
theorem stage26_strictE_formal_polynomial_ode {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial AlgebraicComplex,
      (∃ i, p i ≠ 0) ∧
      ∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex :
          PowerSeries AlgebraicComplex → PowerSeries AlgebraicComplex)^[i.val]
          (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
            (strictEFunctionTaylorRealization f hf)) = 0 := by
  have hode : HasAlgebraicPolynomialODE f := by
    obtain ⟨a, hent, hs, hode, harith⟩ := hf
    exact hode
  obtain ⟨m, p, hp, heq⟩ := hode
  refine ⟨m, p, hp, ?_⟩
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let F := strictEFunctionTaylorRealization f hf
  letI : CommSemiring (subfieldEntireFunctionAlgebra k) :=
    (subfieldEntireFunctionAlgebra k).toCommSemiring
  letI : Algebra k (subfieldEntireFunctionAlgebra k) :=
    (subfieldEntireFunctionAlgebra k).algebra
  letI : Semiring (subfieldEntireFunctionAlgebra k) :=
    @CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring
  letI : AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
    @NonUnitalNonAssocSemiring.toAddCommMonoid _
      (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
        (@Semiring.toNonAssocSemiring _
          (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))
  have hactual : ∑ i, Polynomial.aeval (R := k) (subfieldEntireCoordinate k) (p i) *
      ((subfieldEntireFunctionDerivation k)^[i.val]) F = 0 :=
    (stage14_actualPolynomialRelation_iff k F m p).mpr heq
  have hmap := congrArg (subfieldEntireTaylorAlgHom k) hactual
  have hpoly (i : Fin (m + 1)) :
      subfieldEntireTaylorAlgHom k (Polynomial.aeval (R := k) (subfieldEntireCoordinate k) (p i)) =
        ((show Polynomial k from p i) : PowerSeries k) := stage26_subfieldTaylor_polynomial k (p i)
  simp only [map_sum, map_zero, map_mul, stage26_subfieldTaylor_iterate, hpoly] at hmap
  exact hmap

end StrictEUnit
