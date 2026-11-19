import MonicRootPolynomialEnvelope
import MeromorphicContinuousEnvelope
import EntirePolynomialGrowth
import Mathlib.Analysis.Analytic.Uniqueness

/-!
New reconstruction, not recovered original source.
The analytic bridge from a pointwise monic polynomial relation for a quotient
of entire functions to an actual polynomial quotient.
-/
noncomputable section
open scoped Topology
open Filter Set Polynomial

namespace StrictEUnit

/-- An entire fraction satisfying a monic polynomial relation over ℂ[z] is a
polynomial. Its values at denominator zeros are recovered by analytic extension,
not by assigning the total quotient's default value there. -/
theorem entire_fraction_polynomial_of_monic_relation {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hG0 : G ≠ 0)
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (hroot : ∀ z : ℂ, G z ≠ 0 →
      (p.map (Polynomial.evalRingHom z)).eval (F z / G z) = 0) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, P.eval z * G z = F z := by
  have hm : MeromorphicOn (fun z => F z / G z) Set.univ := by
    intro z hz
    exact (hF.analyticAt z).meromorphicAt.div' (hG.analyticAt z).meromorphicAt
  obtain ⟨H, hH, hHeq, hHb⟩ :=
    exists_entire_of_meromorphic_continuous_envelope hm
      (continuous_monicRootEnvelope p) (quotient_norm_le_monicRootEnvelope hp hroot)
  have heq : ∀ z, G z ≠ 0 → H z = F z / G z := by
    intro z hz
    exact entire_representative_eq_of_continuousAt hH hHeq
      ((hF z).continuousAt.div (hG z).continuousAt hz)
  obtain ⟨C, N, hC, hgrowth⟩ := monicRootEnvelope_polynomial_growth p
  obtain ⟨P, hP, hdeg⟩ := entire_polynomial_of_modulus_growth hH C 0 N (by
    intro z hz
    simpa only [zero_mul, add_zero] using (hHb z).trans (hgrowth z hz))
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, G z₀ ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hG0 (funext hn)
  have hprod : AnalyticOnNhd ℂ (fun z => H z * G z) Set.univ := by
    intro z hz
    exact (hH.analyticAt z).mul (hG.analyticAt z)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z hz => hF.analyticAt z
  have hevent : (fun z => H z * G z) =ᶠ[𝓝 z₀] F := by
    filter_upwards [(hG z₀).continuousAt.eventually_ne hz₀] with z hz
    rw [heq z hz, div_mul_cancel₀ _ hz]
  have hglobal : (fun z => H z * G z) = F := hprod.eq_of_eventuallyEq hFa hevent
  refine ⟨P, fun z => ?_⟩
  rw [hP z]
  exact congrFun hglobal z

end StrictEUnit

#print axioms StrictEUnit.entire_fraction_polynomial_of_monic_relation
