import AllClassSolutionMatrixPrefix
import RegularIndicialBinomialArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Any finite family of number-field coefficients has one derived positive
integer clearing; no growth hypothesis is involved. -/
theorem logJet_finite_family_integral {I : Type*} [Fintype I] (v : I → K) :
    ∃ e : ℕ,0<e ∧ ∀ i,IsIntegral ℤ ((e : K)*v i) := by
  classical
  obtain ⟨e,he,hei⟩ := exists_positive_nat_integral_vector
    (fun j : Fin (Fintype.card I) =>v ((Fintype.equivFin I).symm j))
  refine ⟨e,he,?_⟩
  intro i
  simpa only [Equiv.symm_apply_apply] using hei ((Fintype.equivFin I) i)

/-- The bounded initial log jet is FINITE and hence automatically arithmetic
over the supplied number field. Its integer is independent of the later cutoff. -/
theorem logSolution_fixed_jet_common_denominator {r : ℕ}
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K))) (L W : ℤ) (d : ℕ)
    (hYlow : ∀ i j a,a<L →(logPolynomialToCoefficientSeries (Y i j)).coeff a=0)
    (hYdeg : ∀ i j a,((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree≤d) :
    ∃ e : ℕ,0<e ∧ ∀ i j t k,k≤W →IsIntegral ℤ ((e : K)*((Y i j).coeff t).coeff k) := by
  let M := (W-L).toNat
  let I := (Fin r × Fin r) × Fin (d+1) × Fin (M+1)
  let v : I → K := fun z =>((Y z.1.1 z.1.2).coeff z.2.1.val).coeff (L+(z.2.2.val : ℤ))
  obtain ⟨e,he,hei⟩ := logJet_finite_family_integral v
  refine ⟨e,he,?_⟩
  intro i j t k hk
  by_cases hkl : k<L
  · rw [← logPolynomialToCoefficientSeries_double_coeff,hYlow i j k hkl,Polynomial.coeff_zero,mul_zero]
    exact isIntegral_zero
  · by_cases htd : d<t
    · rw [← logPolynomialToCoefficientSeries_double_coeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hYdeg i j k).trans_lt htd),mul_zero]
      exact isIntegral_zero
    · let n := (k-L).toNat
      have hn : n<M+1 := by dsimp [n,M];omega
      have heq : L+(n : ℤ)=k := by dsimp [n];omega
      have h := hei (⟨(i,j),⟨t,by omega⟩,⟨n,hn⟩⟩ : I)
      dsimp only [v] at h
      simpa only [heq] using h

end StrictEUnit
end
