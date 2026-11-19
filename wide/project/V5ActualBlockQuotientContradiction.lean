import V5UniversalQuotientAnnihilator
import FaithfulBlockGaugeNonvanishing
import V5ActualEntireDerivativeCoordinates
import V5OrdinaryJetBlockAssembly

/-! Actual source-linked norm-quotient contradiction. Prime constant descent,
universal evaluation and faithful single-block independence are all derived.
The supplied annihilator is the exact source quotient's operator. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix Classical
namespace StrictEUnit

theorem actual_block_quotient_ordinary_annihilator_contradiction
    (k : Subfield ℂ) {S κ : Type*} [Fintype S] {r : ℕ}
    (f : Fin r → subfieldEntireFunctionAlgebra k)
    (A : Matrix (Fin r) (Fin r) (RatFunc k))
    (hsystem : ∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (f i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        stage14_subfieldEntireLaurentAlgHom k (f j))
    (t : Polynomial k) (U : Matrix (Fin r) (Fin r) (Polynomial k)) (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
      algebraMap (Polynomial k) (RatFunc k) t * A i j)
    (b : Fin r → κ) (hA : ∀ i j, b i ≠ b j → A i j = 0)
    (idx : S → Fin r)
    (hli : ∀ s, LinearIndependent (RatFunc k)
      (fun j : {j // b j = b (idx s)} => stage14_subfieldEntireLaurentAlgHom k (f j.val)))
    (m : ℕ) (p : Fin (m+1) → Polynomial k)
    (hord : (p (Fin.last m)).eval 1 ≠ 0)
    (hsource : (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (algebraMap (RatFunc k) (LaurentSeries k) (ordinaryPointInverseLinear (1 : k)) *
          ∏ s, stage14_subfieldEntireLaurentAlgHom k (f (idx s)))) = 0) : False := by
  let y : Fin r → LaurentSeries k := fun i => stage14_subfieldEntireLaurentAlgHom k (f i)
  let I := actualEntireRelationIdeal k f
  let J := ordinaryPointGaugedIdeal t U (1 : k) I
  let J0 := J.comap (MvPolynomial.map (algebraMap k (LaurentSeries k)))
  obtain ⟨_, _, _, _, hJ0, hdescent⟩ :=
    actualEntireOrdinaryPrimeGauge_atOne k f A hsystem t U ht hclear
  letI : J0.IsPrime := hJ0
  obtain ⟨s, hs⟩ := universal_quotient_annihilator_exists_variable_mem
    y A hsystem t U ht hclear J0 hdescent idx m p hord hsource
  have hX : MvPolynomial.X (idx s) ∈ J := by
    change MvPolynomial.map (algebraMap k (LaurentSeries k))
      (MvPolynomial.X (idx s)) ∈ J at hs
    simpa only [MvPolynomial.map_X] using hs
  exact ordinaryPointGaugedIdeal_variable_not_mem_of_block_independent
    y A t U hclear (1 : k) b hA (idx s) (hli s) hX

end StrictEUnit

#print axioms StrictEUnit.actual_block_quotient_ordinary_annihilator_contradiction

noncomputable section
open scoped BigOperators
namespace StrictEUnit
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 60000

/-- Ordinary contradiction on an arbitrary finite index type. This preserves
independence on the exact distinguished fibers when transporting to Fin. -/
theorem v5_actual_finite_block_quotient_contradiction
    (k : Subfield ℂ) {I S κ : Type*} [Fintype I] [Fintype S]
    (f : I → subfieldEntireFunctionAlgebra k)
    (A : Matrix I I (RatFunc k))
    (hsystem : ∀ i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (f i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        v5ActualEntireLaurentAlgHom k (f j))
    (t : Polynomial k) (U : Matrix I I (Polynomial k)) (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
      algebraMap (Polynomial k) (RatFunc k) t * A i j)
    (b : I → κ) (hA : ∀ i j, b i ≠ b j → A i j = 0)
    (idx : S → I)
    (hli : ∀ s, LinearIndependent (RatFunc k)
      (fun j : {j // b j = b (idx s)} => v5ActualEntireLaurentAlgHom k (f j.val)))
    (m : ℕ) (p : Fin (m+1) → Polynomial k)
    (hord : (p (Fin.last m)).eval 1 ≠ 0)
    (hsource : (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (algebraMap (RatFunc k) (LaurentSeries k) (ordinaryPointInverseLinear (1 : k)) *
          ∏ s, v5ActualEntireLaurentAlgHom k (f (idx s)))) = 0) : False := by
  classical
  let e := Fintype.equivFin I
  let F := fun i => f (e.symm i)
  let B := fun i j => A (e.symm i) (e.symm j)
  let V := fun i j => U (e.symm i) (e.symm j)
  let c := fun i => b (e.symm i)
  let pick := fun s => e (idx s)
  refine actual_block_quotient_ordinary_annihilator_contradiction k F B ?_ t V ht
    (fun i j => hclear _ _) c (fun i j h => hA _ _ h) pick ?_ m p hord ?_
  · intro i
    change laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (f (e.symm i))) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A (e.symm i) (e.symm j)) *
        v5ActualEntireLaurentAlgHom k (f (e.symm j))
    exact (hsystem (e.symm i)).trans (e.symm.sum_comp (fun j =>
      algebraMap (RatFunc k) (LaurentSeries k) (A (e.symm i) j) *
        v5ActualEntireLaurentAlgHom k (f j))).symm
  · intro s
    let E : {i // c i = c (pick s)} ≃ {j // b j = b (idx s)} := {
      toFun := fun i => ⟨e.symm i.val, by simpa [c, pick] using i.property⟩
      invFun := fun j => ⟨e j.val, by simpa [c, pick] using j.property⟩
      left_inv := fun i => Subtype.ext (e.apply_symm_apply i.val)
      right_inv := fun j => Subtype.ext (e.symm_apply_apply j.val) }
    change LinearIndependent (RatFunc k)
      (fun i : {i // c i = c (pick s)} => v5ActualEntireLaurentAlgHom k (f (e.symm i.val)))
    exact (hli s).comp (fun i => E i) E.injective
  · change (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (algebraMap (RatFunc k) (LaurentSeries k) (ordinaryPointInverseLinear (1 : k)) *
          ∏ s, v5ActualEntireLaurentAlgHom k (f (e.symm (e (idx s)))))) = 0
    simpa only [Equiv.symm_apply_apply] using hsource


/-- The exact quotient of the retained source factors cannot have an ordinary
annihilator at one if each entire derivative block is rationally independent. -/
theorem v5_actual_ordinary_blocks_quotient_contradiction
    (k : Subfield ℂ) {S : Type*} [Fintype S] {n : S → ℕ}
    (f : S → subfieldEntireFunctionAlgebra k)
    (g : ∀ s, Fin (n s) → subfieldEntireFunctionAlgebra k)
    (a : ∀ s, Fin (n s)) (hkeep : ∀ s, g s (a s) = f s)
    (B : ∀ s, Matrix (Fin (n s)) (Fin (n s)) (RatFunc k))
    (T : S → Polynomial k) (U : ∀ s, Matrix (Fin (n s)) (Fin (n s)) (Polynomial k))
    (hT : ∀ s, (T s).eval 1 ≠ 0)
    (hU : ∀ s i j, algebraMap (Polynomial k) (RatFunc k) (U s i j) =
      algebraMap (Polynomial k) (RatFunc k) (T s) * B s i j)
    (hlin : ∀ s, LinearIndependent (RatFunc k)
      (fun j => v5ActualEntireLaurentAlgHom k (g s j)))
    (hsys : ∀ s i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (g s i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B s i j) *
        v5ActualEntireLaurentAlgHom k (g s j))
    (m : ℕ) (p : Fin (m+1) → Polynomial k)
    (hord : (p (Fin.last m)).eval 1 ≠ 0)
    (hsource : (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (algebraMap (RatFunc k) (LaurentSeries k) (ordinaryPointInverseLinear (1 : k)) *
          ∏ s, v5ActualEntireLaurentAlgHom k (f s))) = 0) : False := by
  classical
  obtain ⟨_,hprod,hfiber,hblock,hfull,t,ht,V,hV⟩ :=
    v5_actual_ordinary_jet_blocks_assemble k 1 f g a hkeep B T U hT hU hlin hsys
  exact v5_actual_finite_block_quotient_contradiction k
    (fun i : Σ s, Fin (n s) => g i.1 i.2)
    (Matrix.blockDiagonal' B) hfull t V ht hV (fun i => i.1) hblock
    (fun s => ⟨s,a s⟩) hfiber m p hord (by rw [hprod]; exact hsource)

#print axioms v5_actual_ordinary_blocks_quotient_contradiction
#print axioms v5_actual_finite_block_quotient_contradiction
end StrictEUnit
