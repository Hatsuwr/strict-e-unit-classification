import CoefficientEulerLeibniz

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero solution of the diagonal coordinate equation forces an actual
integer exponent difference and a single log-free Laurent monomial. -/
theorem coefficientEuler_eigenvector_monomial (s : LaurentSeries (Polynomial K))
    (hs : s≠0) (a : K) (he : polynomialCoefficientEuler 1 s=a • s) :
    ∃ n : ℤ,∃ c : K,c≠0 ∧ a=(n:K) ∧ s=HahnSeries.single n (Polynomial.C c) := by
  have hmode (n : ℤ) (hn : s.coeff n≠0) : (n:K)=a ∧ (s.coeff n).natDegree=0 := by
    apply logFirstOrder_polynomial_eigenvector_constant (s.coeff n) hn
    have h := congrArg (fun z : LaurentSeries (Polynomial K) =>z.coeff n) he
    change (n:K) • s.coeff n+(1:K) • (s.coeff n).derivative=a • s.coeff n at h
    simpa only [one_smul] using h
  let n := s.order
  have hn : s.coeff n≠0 := HahnSeries.coeff_order_ne_zero hs
  obtain ⟨ha,hd⟩ := hmode n hn
  have hc : s.coeff n=Polynomial.C ((s.coeff n).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
  refine ⟨n,(s.coeff n).coeff 0,?_,ha.symm,?_⟩
  · intro hz
    exact hn (hc.trans (by rw [hz,map_zero]))
  · apply HahnSeries.ext
    funext k
    by_cases hk : k=n
    · subst k
      rw [HahnSeries.coeff_single_same]
      exact hc
    · rw [HahnSeries.coeff_single_of_ne hk]
      by_contra hzero
      have heq := (hmode k hzero).1.trans ha.symm
      exact hk (Int.cast_injective heq)

end StrictEUnit
end
