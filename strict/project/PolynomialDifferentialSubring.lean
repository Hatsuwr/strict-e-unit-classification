import FourierUniformConjugateGrowth
import Mathlib.Algebra.Polynomial.Lifts

/-! Integral coefficient rings for the actual logarithmic differential action.
These lemmas do not assume that division by an indicial value is integral. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem polynomial_subring_smul (R : Subring K) (c : K) (f : Polynomial K)
    (hc : c∈R) (hf : ∀ j,f.coeff j∈R) : ∀ j,(c • f).coeff j∈R := by
  intro j
  simpa only [Polynomial.coeff_smul,smul_eq_mul] using R.mul_mem hc (hf j)

theorem polynomial_subring_sub (R : Subring K) (f g : Polynomial K)
    (hf : ∀ j,f.coeff j∈R) (hg : ∀ j,g.coeff j∈R) : ∀ j,(f-g).coeff j∈R := by
  intro j
  simpa only [Polynomial.coeff_sub] using R.sub_mem (hf j) (hg j)

theorem polynomial_subring_sum {ι : Type*} (R : Subring K) (s : Finset ι)
    (f : ι → Polynomial K) (hf : ∀ i∈s,∀ j,(f i).coeff j∈R) :
    ∀ j,(∑ i∈s,f i).coeff j∈R := by
  intro j
  rw [Polynomial.finset_sum_coeff]
  exact R.sum_mem (fun i hi => hf i hi j)

theorem polynomial_subring_derivative (R : Subring K) (f : Polynomial K)
    (hf : ∀ j,f.coeff j∈R) : ∀ j,f.derivative.coeff j∈R := by
  intro j
  rw [Polynomial.coeff_derivative]
  exact R.mul_mem (hf _) (R.add_mem (natCast_mem R j) R.one_mem)

theorem polynomial_subring_iterate_derivative (R : Subring K) (f : Polynomial K)
    (hf : ∀ j,f.coeff j∈R) (i : ℕ) :
    ∀ j,((Polynomial.derivative : Polynomial K → Polynomial K)^[i] f).coeff j∈R := by
  induction i with
  | zero => exact hf
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact polynomial_subring_derivative R _ ih

theorem polynomial_subring_differentialOperator (R : Subring K) (P f : Polynomial K)
    (hP : ∀ j,P.coeff j∈R) (hf : ∀ j,f.coeff j∈R) :
    ∀ j,(polynomialDifferentialOperator P f).coeff j∈R := by
  rw [polynomialDifferentialOperator_apply]
  apply polynomial_subring_sum R
  intro i hi
  exact polynomial_subring_smul R _ _ (hP i) (polynomial_subring_iterate_derivative R f hf i)

theorem polynomial_subring_comp (R : Subring K) (P Q : Polynomial K)
    (hP : ∀ j,P.coeff j∈R) (hQ : ∀ j,Q.coeff j∈R) :
    ∀ j,(P.comp Q).coeff j∈R := by
  have lift (f : Polynomial K) (hf : ∀ j,f.coeff j∈R) :
      ∃ g : Polynomial R,g.map R.subtype=f := by
    apply (Polynomial.mem_lifts f).mp
    apply (Polynomial.lifts_iff_coeff_lifts f).mpr
    intro j
    exact ⟨⟨f.coeff j,hf j⟩,rfl⟩
  obtain ⟨P',hP'⟩ := lift P hP
  obtain ⟨Q',hQ'⟩ := lift Q hQ
  intro j
  rw [← hP',← hQ',← Polynomial.map_comp,Polynomial.coeff_map]
  exact ((P'.comp Q').coeff j).property

theorem polynomial_subring_natTranslate (R : Subring K) (P : Polynomial K)
    (hP : ∀ j,P.coeff j∈R) (n : ℕ) :
    ∀ j,(P.comp (Polynomial.X+Polynomial.C (n : K))).coeff j∈R := by
  apply polynomial_subring_comp R P _ hP
  intro j
  rw [Polynomial.coeff_add]
  apply R.add_mem
  · rw [Polynomial.coeff_X]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact natCast_mem R n
    · exact R.zero_mem

end StrictEUnit
end
