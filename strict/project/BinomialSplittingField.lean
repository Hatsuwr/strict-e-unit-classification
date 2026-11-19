import BinomialPrimitiveCombination
import Mathlib.FieldTheory.SplittingField.Construction

noncomputable section
open scoped NumberField
open NumberField IntermediateField Polynomial
namespace StrictEUnit

theorem binomial_minpoly_root
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (a : K) (ha : BinomialPrefixDenominators a) (b : L)
    (hb : b ∈ (minpoly ℚ a).aroots L) : BinomialPrefixDenominators b := by
  let f := (algHomAdjoinIntegralEquiv ℚ (IsIntegral.of_finite ℚ a)).symm ⟨b,hb⟩
  have hg : BinomialPrefixDenominators (AdjoinSimple.gen ℚ a) := by
    apply binomialPrefixDenominators_of_map (algebraMap ℚ⟮a⟯ K)
    simpa only [AdjoinSimple.algebraMap_gen] using ha
  have hm := binomialPrefixDenominators_map f.toRingHom (AdjoinSimple.gen ℚ a) hg
  have he : f (AdjoinSimple.gen ℚ a) = b :=
    algHomAdjoinIntegralEquiv_symm_apply_gen ℚ (IsIntegral.of_finite ℚ a) ⟨b,hb⟩
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he] using hm

theorem binomial_splitting_field_primitive
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (a : K) (ha : BinomialPrefixDenominators a)
    [IsSplittingField ℚ L (minpoly ℚ a)] :
    ∃ c : L, ℚ⟮c⟯ = ⊤ ∧ BinomialPrefixDenominators c := by
  classical
  apply binomial_primitive_of_finite_generators L ((minpoly ℚ a).aroots L).toFinset
  · intro b hb
    exact binomial_minpoly_root a ha b (Multiset.mem_toFinset.mp hb)
  · exact (isSplittingField_iff_intermediateField.mp
      (inferInstance : IsSplittingField ℚ L (minpoly ℚ a))).2

theorem binomial_integral_primitive_of_primitive
    {L : Type*} [Field L] [NumberField L] (c : L)
    (hc : BinomialPrefixDenominators c) (hgen : ℚ⟮c⟯ = ⊤) :
    ∃ b : L, ℚ⟮b⟯ = ⊤ ∧ IsIntegral ℤ b ∧ BinomialPrefixDenominators b := by
  obtain ⟨n,hn,hint,hbin⟩ := binomialPrefixDenominators_exists_integral_multiple c hc
  refine ⟨(n:L)*c, ?_, hint, hbin⟩
  apply top_unique
  rw [← hgen, adjoin_simple_le_iff]
  have hmem := ℚ⟮(n:L)*c⟯.smul_mem (mem_adjoin_simple_self ℚ ((n:L)*c)) (x := (n:ℚ)⁻¹)
  have hnL : (n : L) ≠ 0 := by exact_mod_cast hn.ne'
  simpa only [Algebra.smul_def, map_inv₀, map_natCast, ← mul_assoc,
    inv_mul_cancel₀ hnL, one_mul] using hmem

/-- The literal splitting field of the original minimal polynomial is a
finite Galois number field with an integral arithmetic primitive generator. -/
theorem actual_binomial_normal_closure
    {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : BinomialPrefixDenominators a) :
    NumberField (minpoly ℚ a).SplittingField ∧
    IsGalois ℚ (minpoly ℚ a).SplittingField ∧
    ∃ c : (minpoly ℚ a).SplittingField,
      ℚ⟮c⟯ = ⊤ ∧ IsIntegral ℤ c ∧ BinomialPrefixDenominators c := by
  let L := (minpoly ℚ a).SplittingField
  letI : NumberField L := ⟨⟩
  have hg : IsGalois ℚ L := IsGalois.of_separable_splitting_field
    (Algebra.IsSeparable.isSeparable ℚ a)
  obtain ⟨c,hgen,hbin⟩ := binomial_splitting_field_primitive (L := L) a ha
  exact ⟨inferInstance, hg, binomial_integral_primitive_of_primitive c hbin hgen⟩

end StrictEUnit
end
