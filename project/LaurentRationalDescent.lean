import LaurentRationalBaseChange

/-! New reconstruction, not recovered historical source.
Once a Laurent series over K is proved rational after coefficient extension to
L, coefficient-linear projection descends that rational function to K. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- Rationality descends through arbitrary coefficient-field extensions. The
linear functional used on the denominator is not treated as multiplicative. -/
theorem laurent_rational_descends_of_polynomial_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : LaurentSeries K) (P Q : Polynomial L) (hQ : Q ≠ 0)
    (hrel : algebraMap (Polynomial L) (LaurentSeries L) P =
      algebraMap (Polynomial L) (LaurentSeries L) Q * x.map (algebraMap K L)) :
    ∃ r : RatFunc K, algebraMap (RatFunc K) (LaurentSeries K) r = x := by
  classical
  have hcoeff : ∃ n : ℕ, Q.coeff n ≠ 0 := by
    by_contra h
    push_neg at h
    apply hQ
    ext n
    simpa using h n
  obtain ⟨n, hn⟩ := hcoeff
  have hell : ∃ ell : L →ₗ[K] K, ell (Q.coeff n) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn ((Module.forall_dual_apply_eq_zero_iff K (Q.coeff n)).mp h)
  obtain ⟨ell, hell⟩ := hell
  let p := coefficientLinearPolynomial ell P
  let q := coefficientLinearPolynomial ell Q
  have hq : q ≠ 0 := by
    intro h
    apply hell
    have hc := congrArg (fun a : Polynomial K => a.coeff n) h
    simpa only [q, coefficientLinearPolynomial_coeff, Polynomial.coeff_zero] using hc
  have hrel' : algebraMap (Polynomial K) (LaurentSeries K) p =
      algebraMap (Polynomial K) (LaurentSeries K) q * x := by
    have h := congrArg (coefficientLinearLaurent ell) hrel
    simpa only [coefficientLinearLaurent_mul, coefficientLinearLaurent_polynomial] using h
  let r : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p /
    algebraMap (Polynomial K) (RatFunc K) q
  refine ⟨r, ?_⟩
  have hq' : algebraMap (Polynomial K) (LaurentSeries K) q ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    intro hz
    apply RatFunc.algebraMap_ne_zero hq
    apply (algebraMap (RatFunc K) (LaurentSeries K)).injective
    simpa only [map_zero] using hz
  change algebraMap (RatFunc K) (LaurentSeries K)
    (algebraMap (Polynomial K) (RatFunc K) p /
      algebraMap (Polynomial K) (RatFunc K) q) = x
  rw [map_div₀,
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K),
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
  apply (div_eq_iff hq').mpr
  simpa only [mul_comm] using hrel'

end StrictEUnit
