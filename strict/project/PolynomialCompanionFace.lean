import WeightedCompanionSupport

/-! Literal guarded face coefficients; no replacement numerator family. -/
noncomputable section
namespace StrictEUnit

/-- The negative-index case is zero, rather than a truncated coefficient. -/
def polynomialCompanionFace {K : Type*} [Field K] (n h a : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (j : Fin (n+1)) : K :=
  if (n+1-j.val)*a≤h*T.natTrailingDegree then
    (Polynomial.expand K h (U (Fin.last n) j)).coeff
      (h*T.natTrailingDegree-(n+1-j.val)*a)
  else 0

/-- The face row is extracted from the original polynomialConnectionSequence,
not from an independently chosen solution of a recurrence. -/
def polynomialConnectionFaceRow {K : Type*} [Field K] (n h a : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (m : ℕ) (j : Fin (n+1)) : K :=
  (Polynomial.expand K h (polynomialConnectionSequence T U m 0 j)).coeff
    (irregularPolynomialWeight h T.natTrailingDegree a m j.val)

/-- At the attained nonzero face index the extracted coefficient is the
actual nonzero trailing coefficient. No divisibility is assumed elsewhere. -/
theorem polynomialCompanionFace_ne_zero_of_attained
    {K : Type*} [Field K] (n h a : ℕ) (hh : 0<h)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (j : Fin (n+1)) (hj : U (Fin.last n) j ≠ 0)
    (he : h*T.natTrailingDegree =
      h*(U (Fin.last n) j).natTrailingDegree+(n+1-j.val)*a) :
    polynomialCompanionFace n h a T U j ≠ 0 := by
  have hguard : (n+1-j.val)*a≤h*T.natTrailingDegree := by omega
  have hindex : h*T.natTrailingDegree-(n+1-j.val)*a =
      h*(U (Fin.last n) j).natTrailingDegree := by omega
  rw [polynomialCompanionFace, if_pos hguard, hindex,
    Polynomial.coeff_expand_mul' hh]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hj

end StrictEUnit
end
