import V5ActualMinimalScalarRow
import V5ActualOrdinaryJetBlock

noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000
open scoped Topology BigOperators
open Filter
namespace StrictEUnit

/-- Exact analytic scalar-order predicates agree for the intermediate-field
and subfield presentations of the algebraic numbers in C. -/
theorem v5_algebraic_subfield_annihilator_iff (f : ℂ → ℂ) (n : ℕ) :
    v5HasAnnihilatorOrder AlgebraicComplex f n ↔
      v5HasAnnihilatorOrder (algebraicClosure ℚ ℂ).toSubfield f n := by
  rfl

/-- The order-zero exclusion in the algebraic-number presentation. -/
theorem v5_actual_algebraic_no_order_zero
    (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (hF : F ≠ 0) : ¬ v5HasAnnihilatorOrder AlgebraicComplex F.val.val 0 := by
  intro h
  exact v5_actual_no_order_zero _ F hF
    ((v5_algebraic_subfield_annihilator_iff F.val.val 0).mp h)

/-- An actual minimal algebraic row with a full local family containing a
nonvanishing solution supplies the literal independent ordinary block. -/
theorem v5_actual_algebraic_ordinary_jet_block
    {n : ℕ} (hn : 0 < n) (p : ℕ → Polynomial AlgebraicComplex) (hp : p n ≠ 0)
    (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (hF : ∀ z, v5RowResidual F.val.val n p z = 0)
    (hmin : ∀ m < n, ¬ v5HasAnnihilatorOrder AlgebraicComplex F.val.val m)
    (u : Fin n → ℂ → ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) 1)
    (hind : v5FiniteGermIndependent 1 u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ),
      v5RowResidual (u i) n (fun j => (p j).map (algebraicClosure ℚ ℂ).val.toRingHom) z = 0)
    (hval : ∃ i, u i 1 ≠ 0) :
    let k := (algebraicClosure ℚ ℂ).toSubfield
    ∃ d : Fin n → ℕ, ∃ i₀ : Fin n, d i₀ = 0 ∧
      let g := v5ActualEntireDerivativeCoordinates k F d
      ∃ B : Matrix (Fin n) (Fin n) (RatFunc k),
      ∃ T : Polynomial k, ∃ U : Matrix (Fin n) (Fin n) (Polynomial k),
      T.eval 1 ≠ 0 ∧ g i₀ = F ∧
      LinearIndependent (RatFunc k) (fun i => v5ActualEntireLaurentAlgHom k (g i)) ∧
      (∀ i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (g i)) =
        ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B i j) *
          v5ActualEntireLaurentAlgHom k (g j)) ∧
      ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
        algebraMap (Polynomial k) (RatFunc k) T * B i j := by
  let k := (algebraicClosure ℚ ℂ).toSubfield
  have hm : ∀ m < n, ¬ v5HasAnnihilatorOrder k F.val.val m := by
    intro m hm h
    exact hmin m hm ((v5_algebraic_subfield_annihilator_iff F.val.val m).mpr h)
  have hli := v5_actual_minimal_row_laurent_independent k F n hm
  have hf : ∑ j ∈ Finset.range (n+1), algebraMap (Polynomial k) (LaurentSeries k) (p j) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[j]
        (v5ActualEntireLaurentAlgHom k F) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply (v5_actual_polynomial_row_iff_laurent_row k F n (fun i => p i.val)).mp
    intro z
    have h := hF z
    unfold v5RowResidual at h
    rw [← Fin.sum_univ_eq_sum_range] at h
    exact h
  exact v5_actual_entire_ordinary_jet_block k hn p hp F 1 hf hli u hu hind hode hval

#print axioms v5_algebraic_subfield_annihilator_iff
#print axioms v5_actual_algebraic_no_order_zero
#print axioms v5_actual_algebraic_ordinary_jet_block
end StrictEUnit
