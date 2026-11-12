import MinimalLaurentOrdinaryContradiction
import StrictEDivisionAtOne
import ActualStrictEFrameAvailability
import ActualStrictEMinimalCyclic

/-! Rational factorial coefficients and a zero at one force singularity of
the exact minimal recurrence over the algebraic coefficient closure. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem actual_polynomial_relation_laurent_same_tuple
    (k : Subfield ℂ) (F : subfieldEntireFunctionAlgebra k)
    (m : ℕ) (p : Fin (m+1) → Polynomial k)
    (h : ∀ z : ℂ, ∑ i, (p i).eval₂ k.subtype z * iteratedDeriv i.val F.val.val z = 0) :
    (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (stage14_subfieldEntireLaurentAlgHom k F)) = 0 := by
  have he := (stage14_actualPolynomialRelation_iff k F m p).mpr h
  have hm := congrArg (stage14_subfieldEntireLaurentAlgHom k) he
  simpa only [map_sum, map_mul, map_zero,
    stage14_subfieldEntireLaurentAlgHom_polynomial,
    stage14_subfieldEntireLaurentAlgHom_iterate] using hm

theorem actual_polynomial_mul_laurent_same_source
    (k : Subfield ℂ) (F G : subfieldEntireFunctionAlgebra k)
    (P : Polynomial k)
    (h : ∀ z : ℂ, P.eval₂ k.subtype z * G.val.val z = F.val.val z) :
    algebraMap (Polynomial k) (LaurentSeries k) P *
      stage14_subfieldEntireLaurentAlgHom k G = stage14_subfieldEntireLaurentAlgHom k F := by
  have he : Polynomial.aeval (subfieldEntireCoordinate k) P * G = F := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change stage14_subfieldEntireEvaluation k z
      (Polynomial.aeval (subfieldEntireCoordinate k) P * G) = F.val.val z
    rw [map_mul, stage14_subfieldEntireEvaluation_polynomial]
    exact h z
  have hm := congrArg (stage14_subfieldEntireLaurentAlgHom k) he
  simpa only [map_mul, stage14_subfieldEntireLaurentAlgHom_polynomial] using hm

theorem rational_actualStrictE_minimal_not_regular_at_one
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hfne : f ≠ (fun _ => 0))
    (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z))
    (hz : f 1 = 0) (r : ℕ) (hr : 0 < r) (b : Fin r → RatFunc AlgebraicComplex)
    (hmin : OrdinaryBorelMinimalCyclicData
      (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization f hf)) r b) :
    ¬ (∀ i, ∃ B : PowerSeries AlgebraicComplex,
      HahnSeries.ofPowerSeries ℤ AlgebraicComplex B = ordinaryPointRationalMap 1 (b i)) := by
  obtain ⟨g, hg, hmul⟩ := strictEFunction_divAtOne_of_rational_representation hf a hrat hs hz
  have hgne : g ≠ (fun _ => 0) := by
    intro hg0
    apply hfne
    funext z
    simpa only [hg0, mul_zero] using (hmul z).symm
  obtain ⟨m, s, c, p, hode, _hS⟩ := actualStrictE_scalarNormalFormAvailability g hg hgne
  have hord : (p (Fin.last m)).eval 1 ≠ 0 := by
    rw [hode.leading, Polynomial.eval_monomial, one_pow, mul_one]
    exact hode.coefficient_ne_zero
  have hmulL := actual_polynomial_mul_laurent_same_source
    (algebraicClosure ℚ ℂ).toSubfield
    (strictEFunctionTaylorRealization f hf) (strictEFunctionTaylorRealization g hg)
    (Polynomial.X - Polynomial.C 1)
    (by intro z; simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_one, map_one] using hmul z)
  have hann := actual_polynomial_relation_laurent_same_tuple
    (algebraicClosure ℚ ℂ).toSubfield (strictEFunctionTaylorRealization g hg) m p hode.equation
  exact minimal_laurent_recurrence_not_regular_at_one
    (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (strictEFunctionTaylorRealization f hf))
    (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (strictEFunctionTaylorRealization g hg)) r hr b hmin hmulL m p hord hann

theorem rational_actualStrictE_minimal_denominator_zero_at_one
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hfne : f ≠ (fun _ => 0))
    (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z))
    (hz : f 1 = 0) (r : ℕ) (hr : 0 < r) (b : Fin r → RatFunc AlgebraicComplex)
    (hmin : OrdinaryBorelMinimalCyclicData
      (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization f hf)) r b)
    (T : Polynomial AlgebraicComplex) (U : Fin r → Polynomial AlgebraicComplex)
    (hclear : ∀ i, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (U i) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T * b i) :
    T.eval 1 = 0 := by
  by_contra hT
  apply rational_actualStrictE_minimal_not_regular_at_one hf hfne a hrat hs hz r hr b hmin
  intro i
  exact ⟨_, (ordinaryPointRationalMap_of_clearing 1 (b i) T (U i) hT (hclear i)).symm⟩
/-- Existence and singularity are obtained together from the original actual
strict-E input; no chosen minimal operator is required as an extra input. -/
theorem rational_actualStrictE_exists_singular_minimal
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hfne : f ≠ (fun _ => 0))
    (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z))
    (hz : f 1 = 0) :
    ∃ r : ℕ, 0 < r ∧ ∃ b : Fin r → RatFunc AlgebraicComplex,
      OrdinaryBorelMinimalCyclicData
        (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (strictEFunctionTaylorRealization f hf)) r b ∧
      ¬ (∀ i, ∃ B : PowerSeries AlgebraicComplex,
        HahnSeries.ofPowerSeries ℤ AlgebraicComplex B = ordinaryPointRationalMap 1 (b i)) := by
  obtain ⟨r, hr, b, hmin⟩ := strictEFunction_exists_actualLaurent_minimal_cyclic hf hfne
  exact ⟨r, hr, b, hmin,
    rational_actualStrictE_minimal_not_regular_at_one hf hfne a hrat hs hz r hr b hmin⟩

end StrictEUnit
