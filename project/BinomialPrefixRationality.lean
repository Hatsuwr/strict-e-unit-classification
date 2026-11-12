import BinomialGaloisDegreeOne
import BinomialSplittingField

noncomputable section
open IntermediateField Polynomial
namespace StrictEUnit

/-- The literal normal closure of a binomial-arithmetic algebraic element
has degree one, with no prime-supply or local-place hypotheses. -/
theorem binomial_normal_closure_degree_one
    {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : BinomialPrefixDenominators a) :
    Module.finrank ℚ (minpoly ℚ a).SplittingField = 1 := by
  obtain ⟨hN,hG,c,hgen,hi,hc⟩ := actual_binomial_normal_closure a ha
  letI := hN
  letI := hG
  exact binomial_galois_integral_primitive_degree_one c hgen hi hc

/-- Binomial-prefix denominator growth forces rationality for every
number-field element. All prime supply, finite exceptions, conjugate arithmetic,
and normal-closure primitive generation are discharged by earlier theorems. -/
theorem binomialPrefixDenominators_rational
    {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : BinomialPrefixDenominators a) : ∃ q : ℚ, algebraMap ℚ K q = a := by
  let L := (minpoly ℚ a).SplittingField
  letI : NumberField L := ⟨⟩
  have hd : Module.finrank ℚ L = 1 := binomial_normal_closure_degree_one a ha
  have hai := IsIntegral.of_finite ℚ a
  obtain ⟨b,hb⟩ := Polynomial.exists_root_of_splits (algebraMap ℚ L)
    (Polynomial.SplittingField.splits (minpoly ℚ a)) (ne_of_gt (minpoly.degree_pos hai))
  have hb' : b ∈ (minpoly ℚ a).aroots L := by
    rw [Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hai, hb⟩
  let f := (algHomAdjoinIntegralEquiv ℚ hai).symm ⟨b,hb'⟩
  have hle : Module.finrank ℚ ℚ⟮a⟯ ≤ Module.finrank ℚ L :=
    LinearMap.finrank_le_finrank_of_injective f.injective
  have hpos := Module.finrank_pos (R := ℚ) (M := ℚ⟮a⟯)
  have heq : Module.finrank ℚ ℚ⟮a⟯ = 1 := by omega
  exact (IntermediateField.mem_bot).mp
    (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp heq)

/-- The same result in an arbitrary characteristic-zero field, assuming
only algebraicity of the particular element, by exact descent to Q(a). -/
theorem algebraic_binomialPrefixDenominators_rational
    {K : Type*} [Field K] [CharZero K]
    (a : K) (hi : IsIntegral ℚ a) (ha : BinomialPrefixDenominators a) :
    ∃ q : ℚ, algebraMap ℚ K q = a := by
  letI : FiniteDimensional ℚ ℚ⟮a⟯ := IntermediateField.adjoin.finiteDimensional hi
  letI : NumberField ℚ⟮a⟯ := ⟨⟩
  have hb : BinomialPrefixDenominators (AdjoinSimple.gen ℚ a) := by
    apply binomialPrefixDenominators_of_map (algebraMap ℚ⟮a⟯ K)
    simpa only [AdjoinSimple.algebraMap_gen] using ha
  obtain ⟨q,hq⟩ := binomialPrefixDenominators_rational (AdjoinSimple.gen ℚ a) hb
  refine ⟨q, ?_⟩
  have h := congrArg (algebraMap ℚ⟮a⟯ K) hq
  simpa only [← IsScalarTower.algebraMap_apply, AdjoinSimple.algebraMap_gen] using h

end StrictEUnit
end
