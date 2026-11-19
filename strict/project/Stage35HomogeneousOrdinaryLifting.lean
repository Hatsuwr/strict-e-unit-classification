import Stage35LaurentOrdinarySystem
import Stage34ExactDehomogenization

/-! Exact transport from an explicit homogeneous ordinary-point lifting input.
The homogeneous lifting assertion is NOT proved here. Neither Beukers' theorem
nor the match between our strict-E definition and any published height-based
E-function definition is claimed. The source predicate and its one-way match
remain separate inputs to the generic theorem. -/
noncomputable section
open scoped BigOperators Topology
namespace StrictEUnit

/-- The still-unproved homogeneous input at the ordinary algebraic point 1.
The system is given by actual polynomial numerators B and one denominator t,
with t(1) nonzero. H is homogeneous in function variables, has a genuine local
analytic relation, and specializes LITERALLY to P, not to a scalar multiple.
The outer polynomial variable is the independent complex coordinate. -/
def HomogeneousOrdinaryLiftingAtOne (E : (ℂ → ℂ) → Prop) : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (f : Fin n → entireFunctionAlgebra)
      (t : Polynomial AlgebraicComplex)
      (B : Matrix (Fin n) (Fin n) (Polynomial AlgebraicComplex)),
      t.eval 1 ≠ 0 → (∀ i, E (f i).val) → Stage35ClearedSystem f t B →
      ∀ (D : ℕ), 0 < D → ∀ (P : MvPolynomial (Fin n) AlgebraicComplex),
        P ≠ 0 → P.IsHomogeneous D →
        MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
          (fun i => (f i).val 1) P = 0 →
        ∃ H : Polynomial (MvPolynomial (Fin n) AlgebraicComplex),
          (∀ r, (H.coeff r).IsHomogeneous D) ∧
          stage35_relationResidual f H =ᶠ[𝓝 (1 : ℂ)] 0 ∧ H.eval 1 = P

/-- Exact Beukers-interface transport, without proving the deep homogeneous
input or silently identifying different E-function definitions. No nonempty
premise on the original index type, and no arbitrary relation-lifting premise,
survive in the theorem's inputs. -/
theorem stage35_laurent_lifting_of_source_homogeneous
    (E : (ℂ → ℂ) → Prop)
    (hmatch : ∀ f, IsStrictEFunction f → E f)
    (h : HomogeneousOrdinaryLiftingAtOne E) : StrictELaurentRelationLifting := by
  intro ι _ _ f A hf hs P hP
  classical
  by_cases hzero : P = 0
  · subst P
    exact ⟨0, by simp, by simp⟩
  obtain ⟨N, hN, B, hB, ht, hsys⟩ := stage35_laurent_exists_global_clearing f A hs
  let n := Fintype.card (Option ι)
  let e : Option ι ≃ Fin n := Fintype.equivFin (Option ι)
  let g : Fin n → entireFunctionAlgebra := fun j => stage35_augmentFunctions f (e.symm j)
  let C : Matrix (Fin n) (Fin n) (Polynomial AlgebraicComplex) :=
    fun i j => stage35_augmentMatrix B (e.symm i) (e.symm j)
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨none⟩
  have hg : ∀ i, E (g i).val := fun i =>
    hmatch _ (stage35_augmentFunctions_strict f hf (e.symm i))
  have hgsys : Stage35ClearedSystem g (Polynomial.X ^ N) C :=
    stage35_reindex_clearedSystem e _ _ _ (stage35_augment_clearedSystem f _ B hsys)
  have hvalues (z : ℂ) : (fun j => (g j).val z) =
      fun j => (e.symm j).elim 1 (fun i => (f i).val z) := by
    funext j
    change (stage35_augmentFunctions f (e.symm j)).val z = _
    cases e.symm j <;> rfl
  have hrelation : MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
      (fun j => (g j).val 1) (MvPolynomial.rename e (stage34_hom P)) = 0 := by
    rw [hvalues, stage34_reindexed_hom_eval]
    exact hP
  obtain ⟨H, hhom, hlocal, hexact⟩ := h n hn g (Polynomial.X ^ N) C
    (by rw [ht]; exact one_ne_zero) hg hgsys (P.totalDegree + 1) (Nat.succ_pos _)
    (MvPolynomial.rename e (stage34_hom P)) (stage34_reindexed_hom_ne_zero e hzero)
    (stage34_reindexed_hom_isHomogeneous e P) hrelation
  refine ⟨stage34_reindexedDehomLift e H, ?_,
    stage34_reindexedDehomLift_exact e P H hexact⟩
  have hglobal := stage35_relation_zero_of_local g H hlocal
  intro z
  rw [stage34_reindexedDehomLift_eval₂]
  have hz := hglobal z
  unfold stage35_relationResidual at hz
  rw [hvalues] at hz
  exact hz

/-- Specialization to the homogeneous strict-E normalization. This is still
conditional on that homogeneous assertion, not a proof of Beukers' theorem. -/
theorem stage35_laurent_lifting_of_homogeneous_ordinary
    (h : HomogeneousOrdinaryLiftingAtOne IsStrictEFunction) :
    StrictELaurentRelationLifting :=
  stage35_laurent_lifting_of_source_homogeneous IsStrictEFunction (fun _ hf => hf) h

end StrictEUnit
