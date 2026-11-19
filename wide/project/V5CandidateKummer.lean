import V5AnalyticCandidate
import V5FiniteKummerFactor

noncomputable section
namespace StrictEUnit

/-- Once the actual fixed algebra is known finite, its inclusion into the
realized candidate suffices to produce the marked Kummer map. -/
theorem v5_candidate_finite_marked_kummer
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Algebra K ℂ] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))
    {T : Type*} [CommRing T] [Algebra K T] [Algebra (LaurentPolynomial K) T]
    [IsScalarTower K (LaurentPolynomial K) T] [Module.Finite (LaurentPolynomial K) T]
    (j : T →+* V5WideFieldCandidate A)
    (hj : ∀ p, j (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) (V5WideFieldCandidate A) p) :
    ∃ (q : ℕ) (_ : 0 < q) (α : T →ₐ[K] LaurentPolynomial K),
      α.toRingHom.comp (algebraMap (LaurentPolynomial K) T) = v5LaurentPower q ∧
      ∀ x, LaurentPolynomial.eval₂ (algebraMap K ℂ) 1 (α x) =
        algebraMap K ℂ (v5WideFieldCandidatePoint A (j x)) := by
  obtain ⟨σ, _, hb, hm⟩ := v5_field_candidate_entire_realization (algebraMap K ℂ) A
  let R : entireFunctionAlgebra →+* v5EntireSubalgebra K :=
    { toFun := fun x => ⟨x.val, x.property⟩
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let ρ : T →ₐ[K] v5EntireSubalgebra K :=
    { (R.comp σ).comp j with
      commutes' := by
        intro a
        rw [IsScalarTower.algebraMap_apply K (LaurentPolynomial K) T]
        change R (σ (j (algebraMap (LaurentPolynomial K) T (LaurentPolynomial.C a)))) = _
        rw [hj, hb, v5EntireLaurentEval, LaurentPolynomial.eval₂_C]
        rfl }
  have hbase (p : LaurentPolynomial K) : (ρ (algebraMap (LaurentPolynomial K) T p)).val =
      v5KummerEval (algebraMap K ℂ) 1 p := by
    funext w
    change (σ (j (algebraMap (LaurentPolynomial K) T p))).val w = _
    rw [hj, hb, v5EntireLaurentEval_apply, v5KummerEval_apply]
    have he : Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w) = v5KummerPoint 1 w := by
      apply Units.ext
      simp only [Units.val_mk0, v5KummerPoint_val, Nat.cast_one, div_one]
    rw [he]
  obtain ⟨q, hq, α, hbα, _, hmark⟩ := v5_finite_marked_kummer_factor ρ hbase
  refine ⟨q, hq, α, hbα, fun x => (hmark x).trans ?_⟩
  exact hm (j x)

end StrictEUnit
#print axioms StrictEUnit.v5_candidate_finite_marked_kummer
