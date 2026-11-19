import V5BroadNormQuotientAnnihilator
import V5LaurentJetGaugeVector
import Mathlib.RingTheory.Localization.Integer

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open scoped BigOperators nonZeroDivisors
namespace StrictEUnit
local instance actualMinimumEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) := (subfieldEntireFunctionAlgebra k).toCommRing
local instance actualMinimumEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))



local instance actualMinimumEntireAddGroup (k : Subfield ℂ) :
    AddGroup (subfieldEntireFunctionAlgebra k) :=
  @AddCommGroup.toAddGroup _ (@Ring.toAddCommGroup _
    (@CommRing.toRing _ (subfieldEntireFunctionAlgebra k).toCommRing))

theorem v5_actual_row_zero_of_no_annihilator_through {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ} (hmin : ∀ n ≤ m, ¬ v5HasAnnihilatorOrder K f n)
    (c : ℕ → Polynomial K) (hc : ∀ z, v5RowResidual f m c z = 0) :
    ∀ j ≤ m, c j = 0 := by
  have htop : c m = 0 := by
    by_contra hne
    exact hmin m le_rfl ⟨c, hne, hc⟩
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa [hj0] using htop
  | succ m ih =>
    have hprev : ∀ z, v5RowResidual f m c z = 0 := by
      intro z
      have h := hc z
      unfold v5RowResidual at h ⊢
      simpa only [Finset.sum_range_succ (f := fun j =>
        (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (c j) * iteratedDeriv j f z) (n := m + 1),
        htop, map_zero, zero_mul, add_zero] using h
    intro j hj
    rcases eq_or_lt_of_le hj with h | h
    · simpa [h] using htop
    · exact ih (fun n hn => hmin n (Nat.le_trans hn (Nat.le_succ m))) hprev
        (by by_contra hne; exact hmin m (Nat.le_succ m) ⟨c, hne, hprev⟩) j
        (Nat.le_of_lt_succ h)


/-- Minimality of an actual analytic row implies independence of the literal
Laurent derivative prefix, by clearing a finite rational relation. -/
theorem v5_actual_minimal_row_laurent_independent (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (n : ℕ)
    (hmin : ∀ m < n, ¬ v5HasAnnihilatorOrder k f.val.val m) :
    LinearIndependent (RatFunc k)
      (v5LaurentJet n (stage14_subfieldEntireLaurentAlgHom k f)) := by
  classical
  cases n with
  | zero => exact linearIndependent_empty_type
  | succ m =>
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (Polynomial k)) c
    choose p hp using hb
    have hbne : algebraMap (Polynomial k) (RatFunc k) (b : Polynomial k) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    have heq : ∑ j : Fin (m+1), algebraMap (Polynomial k) (LaurentSeries k) (p j) *
        (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[j.val]
          (stage14_subfieldEntireLaurentAlgHom k f) = 0 := by
      calc
        _ = algebraMap (Polynomial k) (LaurentSeries k) (b : Polynomial k) *
            (∑ j : Fin (m+1), c j • v5LaurentJet (m+1)
              (stage14_subfieldEntireLaurentAlgHom k f) j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k),
            hp j, Algebra.smul_def, map_mul, mul_assoc]
          simp only [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k), Algebra.smul_def, v5LaurentJet]
        _ = 0 := by rw [hc, mul_zero]
    have hactual := (v5_actual_polynomial_row_iff_laurent_row k f m p).mpr heq
    let q : ℕ → Polynomial k := fun j => if h : j < m+1 then p ⟨j,h⟩ else 0
    have hq : ∀ z, v5RowResidual f.val.val m q z = 0 := by
      intro z
      have hh := hactual z
      unfold v5RowResidual
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [v5RowResidual, q] using hh
    have hpi : p i = 0 := by
      have hh := v5_actual_row_zero_of_no_annihilator_through
        (fun l hl => hmin l (Nat.lt_succ_of_le hl)) q hq i.val (Nat.le_of_lt_succ i.isLt)
      simpa [q, i.isLt] using hh
    apply (mul_eq_zero.mp (show algebraMap (Polynomial k) (RatFunc k) (b : Polynomial k) * c i = 0 from ?_)).resolve_left hbne
    rw [← Algebra.smul_def, ← hp i, hpi, map_zero]

/-- A nonzero actual entire function has no order-zero annihilator. -/
theorem v5_actual_no_order_zero (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (hf : f ≠ 0) :
    ¬ v5HasAnnihilatorOrder k f.val.val 0 := by
  rintro ⟨p, hp, heq⟩
  have hactual : ∀ z : ℂ, ∑ i : Fin (0+1),
      (p i.val).eval₂ k.subtype z * iteratedDeriv i.val f.val.val z = 0 := by
    simpa using heq
  have h := (v5_actual_polynomial_row_iff_laurent_row k f 0 (fun i => p i.val)).mp hactual
  change (∑ i : Fin 1, algebraMap (Polynomial k) (LaurentSeries k) (p i.val) *
    (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
      (stage14_subfieldEntireLaurentAlgHom k f)) = 0 at h
  simp only [Fin.sum_univ_one, Fin.val_zero, Function.iterate_zero, id_eq] at h
  have hp' : algebraMap (Polynomial k) (LaurentSeries k) (p 0) ≠ 0 := by
    intro hz
    rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)] at hz
    have hz' := (algebraMap (RatFunc k) (LaurentSeries k)).injective
      (show algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) (p 0)) =
        algebraMap (RatFunc k) (LaurentSeries k) 0 by simpa using hz)
    exact hp (IsFractionRing.to_map_eq_zero_iff.mp hz')
  have hf' : stage14_subfieldEntireLaurentAlgHom k f ≠ 0 := by
    intro hz
    apply hf
    apply stage14_subfieldEntireLaurentAlgHom_injective k
    simpa only [map_zero] using hz
  exact mul_ne_zero hp' hf' h

/-- Existence, positive order, actual minimality, and literal rational
independence are obtained together from any actual annihilator. -/
theorem v5_actual_exists_minimal_scalar_row (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (hf : f ≠ 0)
    (hex : ∃ n, v5HasAnnihilatorOrder k f.val.val n) :
    ∃ n, 0 < n ∧ ∃ p : ℕ → Polynomial k,
      p n ≠ 0 ∧ (∀ z, v5RowResidual f.val.val n p z = 0) ∧
      (∀ m < n, ¬ v5HasAnnihilatorOrder k f.val.val m) ∧
      LinearIndependent (RatFunc k)
        (v5LaurentJet n (stage14_subfieldEntireLaurentAlgHom k f)) := by
  classical
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  have hmin : ∀ m < n, ¬ v5HasAnnihilatorOrder k f.val.val m :=
    fun m hm => Nat.find_min hex hm
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    exact v5_actual_no_order_zero k f hf (hn0 ▸ hn)
  obtain ⟨p,hp,hp0⟩ := hn
  exact ⟨n,hnpos,p,hp,hp0,hmin,v5_actual_minimal_row_laurent_independent k f n hmin⟩

#print axioms v5_actual_no_order_zero
#print axioms v5_actual_minimal_row_laurent_independent
#print axioms v5_actual_exists_minimal_scalar_row
end StrictEUnit
