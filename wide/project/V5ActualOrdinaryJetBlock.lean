import V5LaurentJetGaugeVector
import V5ActualEntireDerivativeCoordinates

noncomputable section
open scoped Topology BigOperators
open Filter
namespace StrictEUnit

/-- One actual ordinary rational block. Its entries are literally bundled
entire derivatives of the supplied function, and one entry is the function. -/
theorem v5_actual_entire_ordinary_jet_block
    (k : Subfield ℂ) {n : ℕ} (hn : 0 < n) (p : ℕ → Polynomial k) (hp : p n ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) (α : k)
    (hf : ∑ j ∈ Finset.range (n+1), algebraMap (Polynomial k) (LaurentSeries k) (p j) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[j]
        (v5ActualEntireLaurentAlgHom k f) = 0)
    (hli : LinearIndependent (RatFunc k) (v5LaurentJet n (v5ActualEntireLaurentAlgHom k f)))
    (u : Fin n → ℂ → ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) (α : ℂ))
    (hind : v5FiniteGermIndependent (α : ℂ) u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (α : ℂ),
      v5RowResidual (u i) n (fun j => (p j).map k.subtype) z = 0)
    (hval : ∃ i, u i (α : ℂ) ≠ 0) :
    ∃ d : Fin n → ℕ, ∃ i₀ : Fin n, d i₀ = 0 ∧
      let g := v5ActualEntireDerivativeCoordinates k f d
      ∃ B : Matrix (Fin n) (Fin n) (RatFunc k),
      ∃ T : Polynomial k, ∃ U : Matrix (Fin n) (Fin n) (Polynomial k),
      T.eval α ≠ 0 ∧ g i₀ = f ∧
      LinearIndependent (RatFunc k) (fun i => v5ActualEntireLaurentAlgHom k (g i)) ∧
      (∀ i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (g i)) =
        ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B i j) *
          v5ActualEntireLaurentAlgHom k (g j)) ∧
      ∀ i j, algebraMap (Polynomial k) (RatFunc k) (U i j) =
        algebraMap (Polynomial k) (RatFunc k) T * B i j := by
  obtain ⟨d,⟨i₀,hi₀⟩,hR,T,hT,U,hU⟩ :=
    v5_analytic_scalar_jetGauge_ordinary hn k.subtype α p hp u hu hind hode hval
  let A := v5NormalizedScalarCompanion p n
  let R := v5SelectedCovariantRows A ⟨0,hn⟩ d
  obtain ⟨hg,hsystem,-⟩ :=
    v5_scalar_laurent_selected_jet_system hn p hp (v5ActualEntireLaurentAlgHom k f) hf hli d hR
  refine ⟨d,i₀,hi₀,v5RationalJetGauge A R,T,U,hT,
    v5_actualEntireDerivativeCoordinates_zero k f d i₀ hi₀,?_,?_,hU⟩
  · simpa only [v5_actualEntireDerivativeCoordinates_laurent] using hg
  · intro i
    simp only [v5_actualEntireDerivativeCoordinates_laurent]
    exact hsystem i

#print axioms v5_actual_entire_ordinary_jet_block
end StrictEUnit
