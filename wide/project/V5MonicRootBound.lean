import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic

noncomputable section
open scoped BigOperators NNReal
namespace StrictEUnit

 theorem v5_monic_root_nnnorm_bound {K : Type*} [NormedDivisionRing K]
    {p : Polynomial K} (hp : p.Monic) {z : K} (hz : p.IsRoot z) :
    ‖z‖₊ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊ := by
  have h := hz.norm_lt_cauchyBound hp.ne_zero
  simp only [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one] at h
  apply h.le.trans
  rw [add_comm (1 : ℝ≥0)]
  apply add_le_add_right
  apply Finset.sup_le
  intro i hi
  exact Finset.single_le_sum (f := fun j => ‖p.coeff j‖₊) (fun j _ => zero_le _) hi

 theorem v5_monic_root_norm_bound {K : Type*} [NormedDivisionRing K]
    {p : Polynomial K} (hp : p.Monic) {z : K} (hz : p.IsRoot z) :
    ‖z‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
  have h := v5_monic_root_nnnorm_bound hp hz
  have h' := (NNReal.coe_le_coe).mpr h
  simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum, coe_nnnorm] using h'

 theorem v5_monic_mapped_root_norm_bound {A : Type*} [CommRing A]
    (φ : A →+* ℂ) {p : Polynomial A} (hp : p.Monic) {z : ℂ}
    (hz : (p.map φ).IsRoot z) :
    ‖z‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖φ (p.coeff i)‖ := by
  have h := v5_monic_root_norm_bound (hp.map φ) hz
  simpa only [hp.natDegree_map φ, Polynomial.coeff_map] using h

/-- Pointwise Kummer-evaluated Laurent-coefficient root bound. No analyticity is assumed. -/
theorem v5_monic_laurent_kummer_root_norm_bound {k : Type*} [CommRing k]
    (ι : k →+* ℂ) (t : ℂˣ) (q : ℕ)
    {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic) {z : ℂ}
    (hz : (p.map (LaurentPolynomial.eval₂ ι (t ^ q))).IsRoot z) :
    ‖z‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree,
      ‖LaurentPolynomial.eval₂ ι (t ^ q) (p.coeff i)‖ :=
  v5_monic_mapped_root_norm_bound (LaurentPolynomial.eval₂ ι (t ^ q)) hp hz

/-- Any finite coefficient majorants give a corresponding root majorant. -/
theorem v5_monic_mapped_root_norm_bound_of_majorants {A : Type*} [CommRing A]
    (φ : A →+* ℂ) {p : Polynomial A} (hp : p.Monic) {z : ℂ}
    (hz : (p.map φ).IsRoot z) (M : ℕ → ℝ)
    (hM : ∀ i ∈ Finset.range p.natDegree, ‖φ (p.coeff i)‖ ≤ M i) :
    ‖z‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, M i := by
  exact (v5_monic_mapped_root_norm_bound φ hp hz).trans
    (add_le_add_left (Finset.sum_le_sum hM) 1)

end StrictEUnit
#print axioms StrictEUnit.v5_monic_root_nnnorm_bound
#print axioms StrictEUnit.v5_monic_root_norm_bound
#print axioms StrictEUnit.v5_monic_mapped_root_norm_bound

#print axioms StrictEUnit.v5_monic_laurent_kummer_root_norm_bound
#print axioms StrictEUnit.v5_monic_mapped_root_norm_bound_of_majorants
