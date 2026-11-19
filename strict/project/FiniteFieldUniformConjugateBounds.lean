import FourierRetainedAmplitudeGrowth
import Mathlib.NumberTheory.NumberField.Embeddings

/-! A fixed finite coefficient field turns separately proved embedding bounds
into ONE bound for every algebraic embedding. Only restrictions that actually
occur are used; no extension-of-embeddings premise is assumed. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- The index type may be infinite. The coefficient field, not the coefficient
set, supplies the finiteness needed to make the geometric constant uniform. -/
theorem finite_field_uniform_weighted_geometric_bound {ι : Type*}
    (E : IntermediateField ℚ AlgebraicComplex) (hE : FiniteDimensional ℚ E)
    (a : ι → ℕ → AlgebraicComplex) (ha : ∀ i n,a i n ∈ E) (w : ℕ → ℝ)
    (h : ∀ φ : AlgebraicComplex →+* ℂ,∃ C : ℝ,1≤C ∧
      ∀ i n,w n*‖φ (a i n)‖ ≤ C^(n+1)) :
    ∃ C : ℝ,1≤C ∧ ∀ (φ : AlgebraicComplex →+* ℂ) i n,
      w n*‖φ (a i n)‖ ≤ C^(n+1) := by
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  have hrestriction : ∀ σ : E →+* ℂ,∃ C : ℝ,1≤C ∧
      ∀ φ : AlgebraicComplex →+* ℂ,φ.comp (algebraMap E AlgebraicComplex)=σ →
      ∀ i n,w n*‖φ (a i n)‖ ≤ C^(n+1) := by
    intro σ
    by_cases hs : ∃ ψ : AlgebraicComplex →+* ℂ,ψ.comp (algebraMap E AlgebraicComplex)=σ
    · obtain ⟨ψ,hψ⟩ := hs
      obtain ⟨C,hC,hbound⟩ := h ψ
      refine ⟨C,hC,?_⟩
      intro φ hφ i n
      have he : φ (a i n)=ψ (a i n) := by
        have hh := congrArg (fun τ : E →+* ℂ => τ ⟨a i n,ha i n⟩) (hφ.trans hψ.symm)
        exact hh
      rw [he]
      exact hbound i n
    · refine ⟨1,le_rfl,?_⟩
      intro φ hφ
      exact (hs ⟨φ,hφ⟩).elim
  choose C hC hb using hrestriction
  let M : ℝ := 1+∑ σ : E →+* ℂ,C σ
  have hsum : 0≤∑ σ : E →+* ℂ,C σ :=
    Finset.sum_nonneg (fun σ hσ => le_trans (by norm_num) (hC σ))
  have hM : 1≤M := by dsimp only [M]; linarith
  refine ⟨M,hM,?_⟩
  intro φ i n
  let σ := φ.comp (algebraMap E AlgebraicComplex)
  have hsingle : C σ ≤ ∑ τ : E →+* ℂ,C τ :=
    Finset.single_le_sum (fun τ hτ => le_trans (by norm_num) (hC τ)) (Finset.mem_univ σ)
  have hle : C σ ≤ M := by dsimp only [M]; linarith
  exact (hb σ φ rfl i n).trans
    (pow_le_pow_left₀ (le_trans (by norm_num) (hC σ)) hle (n+1))

end StrictEUnit
end
