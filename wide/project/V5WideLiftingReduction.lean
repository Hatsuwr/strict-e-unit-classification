import HomogeneousLiftingFromLinear
import V5BroadGaloisNorm

/-! Exact formal relation-lifting reductions for actual wide E-functions.
The linear arithmetic lifting theorem remains an explicit premise here.
No assertion concerning it is added as an axiom. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
open scoped BigOperators Topology
namespace StrictEUnit

theorem v5_wide_tensor_functions {ι : Type*}
    (f : ι → entireFunctionAlgebra) (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (D : ℕ) (hD : 0 < D) :
    ∀ w, V5IsBroadEFunction (liftingTensorPowerFunctions f D w).val := by
  intro w
  have hn : (Finset.univ : Finset (Fin D)).Nonempty :=
    ⟨⟨0, hD⟩, Finset.mem_univ _⟩
  have he : (liftingTensorPowerFunctions f D w).val =
      (fun z => ∏ k : Fin D, (f (w k)).val z) := by
    funext z
    exact tensorWordFunctions_apply f w z
  rw [he]
  simpa using v5_broad_actual_nonempty_product Finset.univ hn
      (fun k => (f (w k)).val) (fun k _ => hf (w k))

theorem v5_wide_augment_functions {ι : Type*} (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, V5IsBroadEFunction (f i).val) :
    ∀ i, V5IsBroadEFunction (stage35_augmentFunctions f i).val := by
  intro i
  cases i with
  | none => simpa [stage35_augmentFunctions] using
      v5_strict_is_broad (algebraic_constant_isStrictEFunction (1 : AlgebraicComplex))
  | some i => exact hf i

def V5WideLinearOrdinaryLiftingInput : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (f : Fin n → entireFunctionAlgebra)
      (t : Polynomial AlgebraicComplex)
      (B : Matrix (Fin n) (Fin n) (Polynomial AlgebraicComplex)),
      t.eval 1 ≠ 0 → (∀ i, V5IsBroadEFunction (f i).val) → Stage35ClearedSystem f t B →
      ∀ (c : Fin n → AlgebraicComplex),
        (∑ i, (c i : ℂ) * (f i).val 1) = 0 →
        ∃ q : Fin n → Polynomial AlgebraicComplex,
          (∀ i, (q i).eval 1 = c i) ∧
          ∀ z : ℂ, ∑ i, (q i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * (f i).val z = 0

/-- Every homogeneous degree is reduced to the same degree-one assertion by
an actual full tensor system, preserving the original t and exact P. -/
theorem v5_wide_homogeneous_lifting_of_linear
    (hlinear : V5WideLinearOrdinaryLiftingInput) :
    HomogeneousOrdinaryLiftingAtOne V5IsBroadEFunction := by
  intro n hn f t B ht hf hs D hD P hP hhom hvalue
  classical
  obtain ⟨p, hp⟩ := homogeneous_eq_sum_tensorWords D P hhom
  let W := Fin D → Fin n
  let m := Fintype.card W
  let e : W ≃ Fin m := Fintype.equivFin W
  let g := liftingTensorPowerFunctions f D
  let C := liftingTensorPowerMatrix B D
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩
  have hg : ∀ u, V5IsBroadEFunction (g u).val := v5_wide_tensor_functions f hf D hD
  have hsys : Stage35ClearedSystem g t C := liftingTensorPower_clearedSystem f t B hs D
  have hval : (∑ u : W, (p u : ℂ) * (g u).val 1) = 0 := by
    rw [hp] at hvalue
    simpa only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      liftingTensorWordForm_eval] using hvalue
  have hval' : (∑ j : Fin m, (p (e.symm j) : ℂ) * (g (e.symm j)).val 1) = 0 :=
    (e.symm.sum_comp (fun u : W => (p u : ℂ) * (g u).val 1)).trans hval
  obtain ⟨q, hq, hqrel⟩ := hlinear m hm (fun j => g (e.symm j)) t
    (fun i j => C (e.symm i) (e.symm j)) ht (fun j => hg (e.symm j))
    (stage35_reindex_clearedSystem e g t C hsys) (fun j => p (e.symm j)) hval'
  apply homogeneousLift_of_coefficient_relations f
    (liftingTensorWordForm (R := AlgebraicComplex) D) D
    (liftingTensorWordForm_homogeneous D) p P hp (fun u => q (e u))
  · intro u
    simpa only [Equiv.symm_apply_apply] using hq (e u)
  · intro z
    simp only [liftingTensorWordForm_eval]
    have he := e.sum_comp (fun j : Fin m =>
      (q j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * (g (e.symm j)).val z)
    simpa only [Equiv.symm_apply_apply] using he.trans (hqrel z)

def V5WideLaurentRelationLifting : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex)),
    (∀ i, V5IsBroadEFunction (f i).val) →
    (∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ)) →
    ∀ P : MvPolynomial ι AlgebraicComplex,
      MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
        (fun i => (f i).val 1) P = 0 →
      ∃ Q : Polynomial (MvPolynomial ι AlgebraicComplex),
        (∀ z : ℂ, Polynomial.eval₂
          (MvPolynomial.eval₂Hom (algebraicClosure ℚ ℂ).val.toRingHom
            (fun i => (f i).val z)) z Q = 0) ∧ Q.eval 1 = P

theorem v5_wide_laurent_lifting_of_homogeneous
    (h : HomogeneousOrdinaryLiftingAtOne V5IsBroadEFunction) : V5WideLaurentRelationLifting := by
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
  have hg : ∀ i, V5IsBroadEFunction (g i).val := fun i =>
    v5_wide_augment_functions f hf (e.symm i)
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


theorem v5_wide_laurent_lifting_of_linear
    (hlinear : V5WideLinearOrdinaryLiftingInput) : V5WideLaurentRelationLifting :=
  v5_wide_laurent_lifting_of_homogeneous (v5_wide_homogeneous_lifting_of_linear hlinear)

#print axioms v5_wide_tensor_functions
#print axioms v5_wide_homogeneous_lifting_of_linear
#print axioms v5_wide_laurent_lifting_of_homogeneous
#print axioms v5_wide_laurent_lifting_of_linear
end StrictEUnit
