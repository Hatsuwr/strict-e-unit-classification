import UniversalQuotientAnnihilator
import FaithfulBlockGaugeNonvanishing

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
