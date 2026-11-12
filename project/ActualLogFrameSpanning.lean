import ActualLogFrameCoordinates

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Actual twisted solutions expand in source-frame columns with constant
coefficients and integer Laurent shifts. A nonzero coefficient forces exponent
class matching. This supplies no denominator or growth claim by itself. -/
theorem actualLogFrame_spanning {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0)
    (xi : K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j) :
    ∃ n : Fin r → ℤ, ∃ c : Fin r → K,
      (∀ j, c j≠0 → rho j-xi=(n j:K)) ∧
      (∀ i, u i=∑ j,logPolynomialToCoefficientSeries (Y i j)*
        HahnSeries.single (n j) (Polynomial.C (c j))) := by
  classical
  obtain ⟨v,hv,hdv⟩ := actualLogFrame_coordinates C rho Y hY hdet xi u hu
  have hm (j : Fin r) : ∃ n : ℤ, ∃ c : K,
      (c≠0 → rho j-xi=(n:K)) ∧ v j=HahnSeries.single n (Polynomial.C c) := by
    by_cases hz : v j=0
    · exact ⟨0,0,by simp,by simp [hz]⟩
    · obtain ⟨n,c,hc,he,hs⟩ := coefficientEuler_eigenvector_monomial (v j) hz _ (hdv j)
      exact ⟨n,c,fun _ =>he,hs⟩
  choose n c hc hs using hm
  refine ⟨n,c,hc,?_⟩
  intro i
  rw [hv i]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j]

/-- A nonzero solution cannot inhabit an exponent class absent from the frame. -/
theorem actualLogFrame_exponent_match {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0)
    (xi : K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j)
    (hne : u≠0) : ∃ j : Fin r, ∃ n : ℤ,rho j-xi=(n:K) := by
  classical
  obtain ⟨n,c,hc,hs⟩ := actualLogFrame_spanning C rho Y hY hdet xi u hu
  by_contra hn
  apply hne
  funext i
  rw [hs i]
  have hz (j : Fin r) : c j=0 := by
    by_contra hj
    exact hn ⟨j,n j,hc j hj⟩
  simp [hz]

end StrictEUnit
end
