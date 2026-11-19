import V5ActualSingleOrdinaryBlock
import V5ActualWideQuotientAnnihilator

noncomputable section
namespace StrictEUnit
local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

/-- Canonical bundling uses a coefficient witness but preserves the literal
entire function. The Laurent embedding is faithful to these coefficients. -/
def v5WideEntire (f : ℂ → ℂ) (hf : V5IsBroadEFunction f) :
    subfieldEntireFunctionAlgebra k :=
  v5FactorialEntire f hf.choose_spec.1 hf.choose hf.choose_spec.2.1

theorem v5_wideEntire_val (f : ℂ → ℂ) (hf : V5IsBroadEFunction f) :
    (v5WideEntire f hf).val.val = f := rfl

/-- Minimum cyclic data that is ordinary at one cannot come from a
nonzero wide E-function vanishing at one. General wide division permits
the contradiction using just one literal independent block. -/
theorem v5_actual_wide_regular_minimal_nonvanishing
    (F : subfieldEntireFunctionAlgebra k) (hf : V5IsBroadEFunction F.val.val)
    (hne : F.val.val ≠ 0) (r : ℕ) (hr : 0 < r) (b : Fin r → RatFunc k)
    (hc : OrdinaryBorelMinimalCyclicData (v5ActualEntireLaurentAlgHom k F) r b)
    (hreg : ∀ i, ∃ S : PowerSeries k,
      HahnSeries.ofPowerSeries ℤ k S = ordinaryPointRationalMap 1 (b i)) :
    F.val.val 1 ≠ 0 := by
  intro hzero
  obtain ⟨m,p,_,hord,hsource⟩ := v5_actual_wide_quotient_ordinary_annihilator F hf hzero hne
  exact v5_actual_minimal_ordinary_block_quotient_impossible F r hr b hc hreg m p hord hsource

#print axioms v5_wideEntire_val
#print axioms v5_actual_wide_regular_minimal_nonvanishing
end StrictEUnit
