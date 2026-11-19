import GaloisNonsplitFiniteExceptions
import Mathlib.FieldTheory.PrimitiveElement

noncomputable section
open scoped NumberField
open NumberField IntermediateField
namespace StrictEUnit

/-- A natural-number coefficient suffices in the two-generator primitive
element argument, preserving the already proved binomial arithmetic closure. -/
theorem exists_nat_primitive_pair
    (K : Type*) [Field K] [NumberField K] (a b : K) :
    ∃ n : ℕ, ℚ⟮a,b⟯ = ℚ⟮a + (n : K)*b⟯ := by
  classical
  letI := Field.finite_intermediateField_of_exists_primitive_element ℚ K
    (Field.exists_primitive_element ℚ K)
  let f : ℕ → IntermediateField ℚ K := fun n => ℚ⟮a + (n : ℚ) • b⟯
  obtain ⟨n,m,hnm,heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hnmQ : (n : ℚ) ≠ (m : ℚ) := by exact_mod_cast hnm
  have hgen : ℚ⟮a,b⟯ = ℚ⟮a + (n : ℚ) • b⟯ := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      have hn : a + (n : ℚ) • b ∈ ℚ⟮a + (n : ℚ) • b⟯ := mem_adjoin_simple_self ℚ _
      have hm : a + (m : ℚ) • b ∈ ℚ⟮a + (m : ℚ) • b⟯ := mem_adjoin_simple_self ℚ _
      dsimp [f] at heq
      rw [← heq] at hm
      have hb := sub_mem hn hm
      rw [show (a + (n : ℚ) • b) - (a + (m : ℚ) • b) =
        ((n : ℚ) - m) • b by rw [sub_smul]; abel] at hb
      replace hb := smul_mem _ hb (x := ((n : ℚ) - m)⁻¹)
      rw [smul_smul, inv_mul_eq_div, div_self (sub_ne_zero.mpr hnmQ), one_smul] at hb
      have ha : a ∈ ℚ⟮a + (n : ℚ) • b⟯ := by
        convert sub_mem hn (smul_mem _ hb (x := (n : ℚ))) using 1
        simp
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      exact ℚ⟮a,b⟯.add_mem (subset_adjoin ℚ {a,b} (Set.mem_insert a {b}))
        (ℚ⟮a,b⟯.smul_mem (subset_adjoin ℚ {a,b} (Set.mem_insert_of_mem a rfl)))
  refine ⟨n, ?_⟩
  simpa only [Algebra.smul_def, map_natCast] using hgen

theorem binomial_primitive_pair
    (K : Type*) [Field K] [NumberField K] (a b : K)
    (ha : BinomialPrefixDenominators a) (hb : BinomialPrefixDenominators b) :
    ∃ c : K, ℚ⟮a,b⟯ = ℚ⟮c⟯ ∧ BinomialPrefixDenominators c := by
  obtain ⟨n,hn⟩ := exists_nat_primitive_pair K a b
  exact ⟨a+(n:K)*b, hn, binomialPrefixDenominators_add a _ ha
    (binomialPrefixDenominators_nat_mul b hb n)⟩

theorem binomial_primitive_finite_family
    (K : Type*) [Field K] [NumberField K] (S : Finset K)
    (hS : ∀ a ∈ S, BinomialPrefixDenominators a) :
    ∃ c : K, IntermediateField.adjoin ℚ (S : Set K) = ℚ⟮c⟯ ∧
      BinomialPrefixDenominators c := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · simpa using (natCast_binomialPrefixDenominators (K := K) 0)
  | insert a S ha ih =>
    obtain ⟨b,hb,hbin⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    obtain ⟨c,hc,hcbin⟩ := binomial_primitive_pair K a b (hS a (Finset.mem_insert_self a S)) hbin
    refine ⟨c, ?_, hcbin⟩
    calc
      IntermediateField.adjoin ℚ (↑(insert a S) : Set K) =
          ℚ⟮a⟯ ⊔ IntermediateField.adjoin ℚ (S : Set K) := by
        rw [Finset.coe_insert, ← Set.singleton_union, IntermediateField.adjoin_union]
      _ = ℚ⟮a,b⟯ := by
        rw [hb, ← IntermediateField.adjoin_union]
        rfl
      _ = ℚ⟮c⟯ := hc

theorem binomial_primitive_of_finite_generators
    (K : Type*) [Field K] [NumberField K] (S : Finset K)
    (hS : ∀ a ∈ S, BinomialPrefixDenominators a)
    (hgen : IntermediateField.adjoin ℚ (S : Set K) = ⊤) :
    ∃ c : K, ℚ⟮c⟯ = ⊤ ∧ BinomialPrefixDenominators c := by
  obtain ⟨c,hc,hbin⟩ := binomial_primitive_finite_family K S hS
  exact ⟨c,hc.symm.trans hgen,hbin⟩

/-- Actual field embeddings preserve the same binomial denominators and bound. -/
theorem binomialPrefixDenominators_map
    {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
    (f : K →+* L) (a : K) (ha : BinomialPrefixDenominators a) :
    BinomialPrefixDenominators (f a) := by
  obtain ⟨C,hC,hden⟩ := ha
  refine ⟨C,hC,?_⟩
  intro N
  obtain ⟨d,hd,hdb,hi⟩ := hden N
  refine ⟨d,hd,hdb,?_⟩
  intro m hm
  have h := (isIntegral_algHom_iff f.toIntAlgHom f.injective).mpr (hi m hm)
  change IsIntegral ℤ (f ((d : K) * ((descPochhammer K m).eval a / (m.factorial : K)))) at h
  rw [← field_choose_eq_descPochhammer_div, map_mul, map_natCast, field_choose_map,
    field_choose_eq_descPochhammer_div] at h
  exact h

end StrictEUnit
end
