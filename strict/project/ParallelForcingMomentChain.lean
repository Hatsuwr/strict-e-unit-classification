import ParallelForcingCompanion

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Parallel eigenmodes with the actual residual exponent pattern admit an
invertible moment change over K and a closed Euler companion chain. -/
theorem residualForcing_moment_chain (s : ℕ) (b d : ℤ)
    (h : Fin s → LaurentSeries (Polynomial K))
    (hh : ∀ j,polynomialCoefficientEuler 1 (h j)=((b+d-(j.val:ℤ):ℤ):K) • h j) :
    let lam : Fin s → K := fun j =>((b+d-(j.val:ℤ):ℤ):K)
    (forcingMomentMatrix lam).det ≠ 0 ∧
    ∃ a : Fin s → K,
      (∀ m,polynomialCoefficientEuler 1 (forcingMoment lam h m)=forcingMoment lam h (m+1)) ∧
      forcingMoment lam h s=∑ m : Fin s,a m • forcingMoment lam h m.val ∧
      forcingMoment lam h 0=∑ j,h j := by
  intro lam
  have hi : Function.Injective lam := shiftedResidualEigenvalues_injective s b d
  obtain ⟨a,ha⟩ := forcingMoment_closure_coefficients lam hi
  exact ⟨forcingMomentMatrix_det_ne_zero lam hi,a,
    forcingMoment_euler lam h hh,forcingMoment_closure lam a h ha,forcingMoment_zero lam h⟩

end StrictEUnit
end
