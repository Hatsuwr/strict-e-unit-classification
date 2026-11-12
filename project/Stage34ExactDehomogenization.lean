import Stage34PolynomialHomogenization
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Coefficientwise dehomogenization preserves literal specialization at one.
The outer polynomial variable is distinct from the added function variable.
An arbitrary equivalence permits finite reindexing without nonemptiness
assumptions on the original variable type. -/
noncomputable section
namespace StrictEUnit

variable {R S ι τ : Type*} [CommSemiring R] [CommSemiring S]

/-- Apply dehomogenization to each coefficient of a polynomial in a separate variable. -/
def stage34_dehomLift (H : Polynomial (MvPolynomial (Option ι) R)) :
    Polynomial (MvPolynomial ι R) :=
  H.map (stage34_dehom R ι)

theorem stage34_dehomLift_eval_one (H : Polynomial (MvPolynomial (Option ι) R)) :
    (stage34_dehomLift H).eval 1 = stage34_dehom R ι (H.eval 1) :=
  Polynomial.eval_one_map _ H

/-- Exact specialization has no scalar or denominator multiplier. -/
theorem stage34_dehomLift_exact (P : MvPolynomial ι R)
    (H : Polynomial (MvPolynomial (Option ι) R)) (hH : H.eval 1 = stage34_hom P) :
    (stage34_dehomLift H).eval 1 = P := by
  rw [stage34_dehomLift_eval_one, hH, stage34_dehom_hom]

/-- Transport the entire polynomial residual, not only its specialization. -/
theorem stage34_dehomLift_eval₂ (κ : R →+* S) (v : ι → S) (z : S)
    (H : Polynomial (MvPolynomial (Option ι) R)) :
    Polynomial.eval₂ (MvPolynomial.eval₂Hom κ v) z (stage34_dehomLift H) =
      Polynomial.eval₂ (MvPolynomial.eval₂Hom κ (fun o => o.elim 1 v)) z H := by
  rw [stage34_dehomLift, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext (stage34_eval_dehom κ v)

/-- Undo a reindexing and then set the added coordinate equal to one. -/
def stage34_unrenameDehom (e : Option ι ≃ τ) :
    MvPolynomial τ R →+* MvPolynomial ι R :=
  (stage34_dehom R ι).comp (MvPolynomial.rename e.symm).toRingHom

@[simp]
theorem stage34_unrenameDehom_rename (e : Option ι ≃ τ)
    (Q : MvPolynomial (Option ι) R) :
    stage34_unrenameDehom (R := R) e (MvPolynomial.rename e Q) =
      stage34_dehom R ι Q := by
  simp [stage34_unrenameDehom, MvPolynomial.rename_rename]

theorem stage34_reindexed_hom_isHomogeneous (e : Option ι ≃ τ)
    (P : MvPolynomial ι R) :
    (MvPolynomial.rename e (stage34_hom P)).IsHomogeneous (P.totalDegree + 1) :=
  (stage34_hom_isHomogeneous P).rename_isHomogeneous

theorem stage34_reindexed_hom_ne_zero (e : Option ι ≃ τ)
    {P : MvPolynomial ι R} (hP : P ≠ 0) :
    MvPolynomial.rename e (stage34_hom P) ≠ 0 := by
  intro h
  apply hP
  have := congrArg (stage34_unrenameDehom (R := R) e) h
  simpa only [stage34_unrenameDehom_rename, stage34_dehom_hom, map_zero] using this

theorem stage34_unrenameDehom_eval (e : Option ι ≃ τ)
    (κ : R →+* S) (v : ι → S) (Q : MvPolynomial τ R) :
    MvPolynomial.eval₂ κ v (stage34_unrenameDehom e Q) =
      MvPolynomial.eval₂ κ (fun j => (e.symm j).elim 1 v) Q := by
  rw [stage34_unrenameDehom, RingHom.comp_apply]
  change MvPolynomial.eval₂ κ v
    (stage34_dehom R ι (MvPolynomial.rename e.symm Q)) = _
  rw [stage34_eval_dehom, MvPolynomial.eval₂_rename]
  rfl

theorem stage34_reindexed_hom_eval (e : Option ι ≃ τ)
    (κ : R →+* S) (v : ι → S) (P : MvPolynomial ι R) :
    MvPolynomial.eval₂ κ (fun j => (e.symm j).elim 1 v)
      (MvPolynomial.rename e (stage34_hom P)) = MvPolynomial.eval₂ κ v P := by
  rw [← stage34_unrenameDehom_eval, stage34_unrenameDehom_rename, stage34_dehom_hom]

/-- The one coefficient map simultaneously undoes renaming and dehomogenizes. -/
def stage34_reindexedDehomLift (e : Option ι ≃ τ)
    (H : Polynomial (MvPolynomial τ R)) : Polynomial (MvPolynomial ι R) :=
  H.map (stage34_unrenameDehom e)

theorem stage34_reindexedDehomLift_exact (e : Option ι ≃ τ)
    (P : MvPolynomial ι R) (H : Polynomial (MvPolynomial τ R))
    (hH : H.eval 1 = MvPolynomial.rename e (stage34_hom P)) :
    (stage34_reindexedDehomLift e H).eval 1 = P := by
  rw [stage34_reindexedDehomLift, Polynomial.eval_one_map, hH,
    stage34_unrenameDehom_rename, stage34_dehom_hom]

theorem stage34_reindexedDehomLift_eval₂ (e : Option ι ≃ τ)
    (κ : R →+* S) (v : ι → S) (z : S) (H : Polynomial (MvPolynomial τ R)) :
    Polynomial.eval₂ (MvPolynomial.eval₂Hom κ v) z (stage34_reindexedDehomLift e H) =
      Polynomial.eval₂ (MvPolynomial.eval₂Hom κ (fun j => (e.symm j).elim 1 v)) z H := by
  rw [stage34_reindexedDehomLift, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext (stage34_unrenameDehom_eval e κ v)

end StrictEUnit
