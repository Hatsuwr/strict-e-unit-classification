import FallingCompositeFilterIdentities
import LiteralLogFilterCoefficientExtraction

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- ONE normalized polynomial filter for all listed exponent classes. It
annihilates a finite prefix; it is not a projector onto any class. -/
def allClassPrefixFilter {q : ℕ} (rho : Fin q → K) (L : ℤ) (N d : ℕ) : Polynomial K :=
  (fallingCompositeSymbol (fun i =>rho i+(L : K)) id (fun _ =>N))^(d+1)

/-- Each class contributes a genuine root throughout the chosen integer
window, regardless of whether other classes differ by integers. -/
theorem allClassPrefixFilter_root {q : ℕ} (rho : Fin q → K)
    (L : ℤ) (N : ℕ) (i : Fin q) (n : ℕ) (hn : n<N) :
    (fallingCompositeSymbol (fun i =>rho i+(L : K)) id (fun _ =>N)).IsRoot
      (rho i+((L+(n : ℤ) : ℤ) : K)) := by
  rw [Polynomial.IsRoot,fallingCompositeSymbol,Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,id_eq]
  rw [show rho i+((L+(n : ℤ) : ℤ) : K)-(rho i+(L : K))=(n : K) by push_cast;ring,
    normalizedFallingSymbol_eval,Ring.choose_natCast,Nat.choose_eq_zero_of_lt hn,Nat.cast_zero]

/-- Repeating the whole multi-class filter d+1 times kills every logarithmic
polynomial of degree <=d at EVERY targeted class/index. -/
theorem allClassPrefixFilter_kills_log_coefficient {q : ℕ} (rho : Fin q → K)
    (L : ℤ) (N d : ℕ) (i : Fin q) (n : ℕ) (hn : n<N)
    (f : Polynomial K) (hf : f.natDegree≤d) :
    shiftedPolynomialDifferentialOperator (rho i+((L+(n : ℤ) : ℤ) : K))
      (allClassPrefixFilter rho L N d) f=0 := by
  by_cases hP : allClassPrefixFilter rho L N d=0
  · simp only [hP,shiftedPolynomialDifferentialOperator,map_zero,LinearMap.zero_apply]
  · apply (shiftedPolynomialDifferentialOperator_kernel_iff _ _ _ hP).2
    have hd : (Polynomial.X-Polynomial.C (rho i+((L+(n : ℤ) : ℤ) : K)))^(d+1)∣
        allClassPrefixFilter rho L N d :=
      pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr (allClassPrefixFilter_root rho L N i n hn)) (d+1)
    have hm := (Polynomial.le_rootMultiplicity_iff hP).2 hd
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hf)
      (by exact_mod_cast (show d<(allClassPrefixFilter rho L N d).rootMultiplicity
        (rho i+((L+(n : ℤ) : ℤ) : K)) by omega))

/-- Literal Laurent/log coefficients vanish throughout the full low prefix.
The lower support and log-degree bounds are explicit inputs, not arithmetic
assumptions. rho is arbitrary; no exponent z^rho is inserted in this ring. -/
theorem allClassPrefixFilter_literal_prefix_zero {q : ℕ} (rho : Fin q → K)
    (L : ℤ) (N d : ℕ) (i : Fin q) (f : Polynomial (LaurentSeries K))
    (hlow : ∀ a : ℤ,a<L →(logPolynomialToCoefficientSeries f).coeff a=0)
    (hdeg : ∀ a : ℤ,((logPolynomialToCoefficientSeries f).coeff a).natDegree≤d)
    (a : ℤ) (ha : a<L+(N : ℤ)) :
    (logPolynomialToCoefficientSeries (literalLogPolynomialFilter (rho i)
      (allClassPrefixFilter rho L N d) f)).coeff a=0 := by
  rw [literalLogPolynomialFilter_coefficient]
  by_cases hal : a<L
  · rw [hlow a hal,map_zero]
  · let n := (a-L).toNat
    have hn : n<N := by dsimp [n];omega
    have he : L+(n : ℤ)=a := by dsimp [n];omega
    simpa only [he] using allClassPrefixFilter_kills_log_coefficient rho L N d i n hn
      ((logPolynomialToCoefficientSeries f).coeff a) (hdeg a)

/-- The same prefix statement for each actual logarithmic coefficient. -/
theorem allClassPrefixFilter_literal_double_prefix_zero {q : ℕ} (rho : Fin q → K)
    (L : ℤ) (N d : ℕ) (i : Fin q) (f : Polynomial (LaurentSeries K))
    (hlow : ∀ a : ℤ,a<L →(logPolynomialToCoefficientSeries f).coeff a=0)
    (hdeg : ∀ a : ℤ,((logPolynomialToCoefficientSeries f).coeff a).natDegree≤d)
    (a : ℤ) (ha : a<L+(N : ℤ)) (j : ℕ) :
    ((literalLogPolynomialFilter (rho i) (allClassPrefixFilter rho L N d) f).coeff j).coeff a=0 := by
  rw [← logPolynomialToCoefficientSeries_double_coeff,
    allClassPrefixFilter_literal_prefix_zero rho L N d i f hlow hdeg a ha,Polynomial.coeff_zero]

end StrictEUnit
end
