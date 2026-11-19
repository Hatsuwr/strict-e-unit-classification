import HomogeneousLiftingWordSpan
import Stage35HomogeneousOrdinaryLifting

/-! The complete finite-degree reduction. The degree-one arithmetic theorem
is an explicit premise, never registered as an axiom or proved by this file. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Topology
namespace StrictEUnit

/-- The remaining linear arithmetic specialization assertion. It includes
zero coefficient vectors and asks for exact values of each coefficient. -/
def StrictELinearOrdinaryLiftingAtOne : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (f : Fin n → entireFunctionAlgebra)
      (t : Polynomial AlgebraicComplex)
      (B : Matrix (Fin n) (Fin n) (Polynomial AlgebraicComplex)),
      t.eval 1 ≠ 0 → (∀ i, IsStrictEFunction (f i).val) → Stage35ClearedSystem f t B →
      ∀ (c : Fin n → AlgebraicComplex),
        (∑ i, (c i : ℂ) * (f i).val 1) = 0 →
        ∃ q : Fin n → Polynomial AlgebraicComplex,
          (∀ i, (q i).eval 1 = c i) ∧
          ∀ z : ℂ, ∑ i, (q i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * (f i).val z = 0

/-- Every homogeneous degree is reduced to the same degree-one assertion by
an actual full tensor system, preserving the original t and exact P. -/
theorem homogeneousOrdinaryLifting_of_linear
    (hlinear : StrictELinearOrdinaryLiftingAtOne) :
    HomogeneousOrdinaryLiftingAtOne IsStrictEFunction := by
  intro n hn f t B ht hf hs D hD P hP hhom hvalue
  classical
  obtain ⟨p, hp⟩ := homogeneous_eq_sum_tensorWords D P hhom
  let W := Fin D → Fin n
  let m := Fintype.card W
  let e : W ≃ Fin m := Fintype.equivFin W
  let g := liftingTensorPowerFunctions f D
  let C := liftingTensorPowerMatrix B D
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩
  have hg : ∀ u, IsStrictEFunction (g u).val := liftingTensorPowerFunctions_strict f hf D
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

/-- The already checked dehomogenization converts that linear arithmetic input
into the exact Laurent relation-lifting interface used downstream. -/
theorem strictELaurentLifting_of_linear
    (hlinear : StrictELinearOrdinaryLiftingAtOne) : StrictELaurentRelationLifting :=
  stage35_laurent_lifting_of_homogeneous_ordinary (homogeneousOrdinaryLifting_of_linear hlinear)

end StrictEUnit
