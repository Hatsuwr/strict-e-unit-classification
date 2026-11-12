import Stage41ArithmeticMinimalConnection
import SelectedRegularCompanionData

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

theorem stage41_same_selected_regular_companion
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex,
    ∃ hmem : ∀ n, a n ∈ F, ∃ hNF : NumberField F,
    ∃ r : ℕ, ∃ hr : 0 < r, ∃ c : Fin r → RatFunc F,
    ∃ T : Polynomial (𝓞 F),
    ∃ UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 F)), ∃ E : ℝ,
      @SelectedRegularCompanionData F AlgebraicComplex _ hNF _
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))
        (PowerSeries.mk a) (algebraMap F AlgebraicComplex) r hr c T UI E := by
  obtain ⟨m,qOriginal,F,hmem,qFOriginal,hfinite,hmap,hq,hqF,hodeOriginal,hpackage,harith⟩ :=
    stage41_same_input_arithmetic_minimal_connection a ha hne
  obtain ⟨hNF,r,hr,c,hdata⟩ := hpackage
  letI : NumberField F := hNF
  let G : PowerSeries F := PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)
  let φ : F →+* AlgebraicComplex := algebraMap F AlgebraicComplex
  have hGH : PowerSeries.map φ G = PowerSeries.mk a := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rfl
  obtain ⟨T,UI,E,hpacket⟩ := exists_selectedRegularCompanionData
    G (PowerSeries.mk a) φ r hr c hdata hGH
  exact ⟨F,hmem,hNF,r,hr,c,T,UI,E,hpacket⟩

end StrictEUnit
end
