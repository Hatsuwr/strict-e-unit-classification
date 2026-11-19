import AllClassSolutionMatrixPrefix

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Every finite Laurent matrix has a common integral lower-support bound.
It is derived from the entries, not a regularity assumption. -/
theorem laurentMatrix_exists_fixed_pole_bound {R : Type*} [CommRing R] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries R)) :
    ∃ W : ℕ,∀ i j a,a< -(W : ℤ) →(A i j).coeff a=0 := by
  let W := ∑ i,∑ j,(A i j).order.natAbs
  refine ⟨W,?_⟩
  intro i j a ha
  have h1 : (A i j).order.natAbs≤∑ j,(A i j).order.natAbs :=
    Finset.single_le_sum (f:=fun j : Fin r =>(A i j).order.natAbs) (fun j _ =>Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j,(A i j).order.natAbs)≤W :=
    Finset.single_le_sum (f:=fun i : Fin r =>∑ j,(A i j).order.natAbs) (fun i _ =>Nat.zero_le _) (Finset.mem_univ i)
  have habs : -(A i j).order≤((A i j).order.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a:= -(A i j).order))
  exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

variable {K : Type*} [Field K] [CharZero K]

/-- Taking a Laurent coefficient cannot increase a finite polynomial-log degree. -/
theorem logCoefficient_natDegree_le (f : Polynomial (LaurentSeries K)) (a : ℤ) :
    ((logPolynomialToCoefficientSeries f).coeff a).natDegree≤f.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro t ht
  rw [logPolynomialToCoefficientSeries_double_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt ht,HahnSeries.coeff_zero]

/-- A finite matrix of polynomial-log Laurent entries supplies its own uniform
lower-support and log-degree bounds. These bounds do not assert arithmetic. -/
theorem logFrame_exists_uniform_bounds {r : ℕ}
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K))) :
    ∃ L : ℤ,∃ d : ℕ,
      (∀ i j a,a<L →(logPolynomialToCoefficientSeries (Y i j)).coeff a=0) ∧
      (∀ i j a,((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree≤d) := by
  obtain ⟨W,hW⟩ := laurentMatrix_exists_fixed_pole_bound
    (Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j)))
  refine ⟨-(W : ℤ),∑ i,∑ j,(Y i j).natDegree,hW,?_⟩
  intro i j a
  apply (logCoefficient_natDegree_le (Y i j) a).trans
  have h1 : (Y i j).natDegree≤∑ j,(Y i j).natDegree :=
    Finset.single_le_sum (f:=fun j : Fin r =>(Y i j).natDegree)
      (fun j _ =>Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j,(Y i j).natDegree)≤∑ i,∑ j,(Y i j).natDegree :=
    Finset.single_le_sum (f:=fun i : Fin r =>∑ j,(Y i j).natDegree)
      (fun i _ =>Nat.zero_le _) (Finset.mem_univ i)
  exact h1.trans h2

end StrictEUnit
end
