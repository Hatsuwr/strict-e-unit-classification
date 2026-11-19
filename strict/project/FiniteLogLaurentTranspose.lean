import LaurentLogSeriesEmbedding

/-!
# Uniformly finite logarithmic degree in the exact Laurent-log source

The Stage43 source matrix has entries in `Polynomial (LaurentSeries K)`.
A Laurent series with polynomial coefficients represents such an entry exactly
when its log degrees have one common bound. Individual finiteness at each
Laurent exponent does not suffice. This file constructs that representation
and checks the actual Euler-plus-log operator by literal coefficients.
It does not assert source-basis availability or André's theorem.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- One bound applies to the log degree at every Laurent exponent. -/
def HasUniformLogBound (s : LaurentSeries (Polynomial K)) (d : ℕ) : Prop :=
  ∀ n j, d ≤ j → (s.coeff n).coeff j = 0

/-- Transpose the first d log coefficients. The Laurent supports may be infinite. -/
def finiteLogLaurentTranspose (d : ℕ) (s : LaurentSeries (Polynomial K)) :
    Polynomial (LaurentSeries K) :=
  ∑ j ∈ Finset.range d, Polynomial.monomial j (s.map (Polynomial.lcoeff K j))

/-- The truncation formula is valid without a bounded-degree assumption. -/
theorem finiteLogLaurentTranspose_coeff (d : ℕ)
    (s : LaurentSeries (Polynomial K)) (j : ℕ) :
    (finiteLogLaurentTranspose d s).coeff j =
      if j < d then s.map (Polynomial.lcoeff K j) else 0 := by
  classical
  simp [finiteLogLaurentTranspose, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]

/-- Under the uniform bound, no scalar coefficient is changed or omitted. -/
theorem finiteLogLaurentTranspose_double_coeff (d : ℕ)
    (s : LaurentSeries (Polynomial K)) (hs : HasUniformLogBound s d)
    (j : ℕ) (n : ℤ) :
    ((finiteLogLaurentTranspose d s).coeff j).coeff n = (s.coeff n).coeff j := by
  rw [finiteLogLaurentTranspose_coeff]
  split_ifs with h
  · rfl
  · exact (hs n j (Nat.le_of_not_gt h)).symm

/-- The produced source polynomial is uniquely determined by its double coefficients. -/
theorem finiteLogLaurentTranspose_unique (d : ℕ)
    (s : LaurentSeries (Polynomial K)) (hs : HasUniformLogBound s d)
    (p : Polynomial (LaurentSeries K))
    (hp : ∀ j n, (p.coeff j).coeff n = (s.coeff n).coeff j) :
    p = finiteLogLaurentTranspose d s := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  rw [finiteLogLaurentTranspose_double_coeff d s hs, hp]

/-- Enlarging the chosen bound leaves the represented source element unchanged. -/
theorem finiteLogLaurentTranspose_bound_independent (d e : ℕ)
    (s : LaurentSeries (Polynomial K)) (hd : HasUniformLogBound s d)
    (he : HasUniformLogBound s e) :
    finiteLogLaurentTranspose d s = finiteLogLaurentTranspose e s :=
  finiteLogLaurentTranspose_unique e s he _
    (finiteLogLaurentTranspose_double_coeff d s hd)

/-- Exact representation criterion for the ambient used by Stage43 and Stage45.
A merely coefficientwise-finite logarithm is not silently treated as finite-log. -/
theorem exists_logPolynomial_iff_uniform_log_bound
    (s : LaurentSeries (Polynomial K)) :
    (∃ p : Polynomial (LaurentSeries K),
      ∀ j n, (p.coeff j).coeff n = (s.coeff n).coeff j) ↔
      ∃ d : ℕ, HasUniformLogBound s d := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.natDegree + 1, ?_⟩
    intro n j hj
    rw [← hp j n, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    rfl
  · rintro ⟨d, hd⟩
    exact ⟨finiteLogLaurentTranspose d s, finiteLogLaurentTranspose_double_coeff d s hd⟩

/-- A recurrence-generated polynomial coefficient sequence with one common
log bound gives an actual bounded-log Laurent series, with no negative powers. -/
theorem uniformLogBound_powerSeries_mk (a : ℕ → Polynomial K) (d : ℕ)
    (ha : ∀ n j, d ≤ j → (a n).coeff j = 0) :
    HasUniformLogBound ((PowerSeries.mk a : PowerSeries (Polynomial K)) :
      LaurentSeries (Polynomial K)) d := by
  intro n j hj
  rw [PowerSeries.coeff_coe]
  split_ifs
  · exact Polynomial.coeff_zero j
  · rw [PowerSeries.coeff_mk]
    exact ha n.natAbs j hj

/-- The source polynomial built from a coefficient recurrence retains every
natural-exponent/log-degree coefficient exactly. -/
theorem finiteLogLaurentTranspose_powerSeries_mk_coeff (a : ℕ → Polynomial K)
    (d : ℕ) (ha : ∀ n j, d ≤ j → (a n).coeff j = 0) (j n : ℕ) :
    ((finiteLogLaurentTranspose d
      ((PowerSeries.mk a : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K))).coeff j).coeff n =
      (a n).coeff j := by
  rw [finiteLogLaurentTranspose_double_coeff d _ (uniformLogBound_powerSeries_mk a d ha),
    LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mk]

/-- Euler in the Laurent variable plus N times the formal log derivative,
written on polynomial-valued Laurent coefficients. Its support is a subset
of the input support, so the construction is an actual Laurent series. -/
def polynomialCoefficientEuler (N : K) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial K) where
  coeff n := (n : K) • s.coeff n + N • (s.coeff n).derivative
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn
    change s.coeff n ≠ 0
    intro hz
    apply hn
    simp [hz])

/-- The coefficient-level source operator preserves the same global log bound. -/
theorem polynomialCoefficientEuler_uniform_bound (N : K)
    (s : LaurentSeries (Polynomial K)) (d : ℕ) (hs : HasUniformLogBound s d) :
    HasUniformLogBound (polynomialCoefficientEuler N s) d := by
  intro n j hj
  change (((n : K) • s.coeff n + N • (s.coeff n).derivative).coeff j) = 0
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_derivative,
    hs n j hj, hs n (j+1) (by omega), smul_zero, zero_mul, add_zero]

/-- Literal differential intertwining in Polynomial (LaurentSeries K).
The logarithm parameter is N and the Laurent exponent is not rescaled. -/
theorem finiteLogLaurentTranspose_euler (N : K) (d : ℕ)
    (s : LaurentSeries (Polynomial K)) (hs : HasUniformLogBound s d) :
    finiteLogLaurentTranspose d (polynomialCoefficientEuler N s) =
      logPolynomialEuler N (finiteLogLaurentTranspose d s) := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  rw [finiteLogLaurentTranspose_double_coeff d _
      (polynomialCoefficientEuler_uniform_bound N s d hs),
    logPolynomialEuler_double_coeff,
    finiteLogLaurentTranspose_double_coeff d s hs,
    finiteLogLaurentTranspose_double_coeff d s hs]
  change (((n : K) • s.coeff n + N • (s.coeff n).derivative).coeff j) = _
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_derivative,
    smul_eq_mul]

end StrictEUnit

#print axioms StrictEUnit.HasUniformLogBound
#print axioms StrictEUnit.finiteLogLaurentTranspose
#print axioms StrictEUnit.finiteLogLaurentTranspose_coeff
#print axioms StrictEUnit.finiteLogLaurentTranspose_double_coeff
#print axioms StrictEUnit.finiteLogLaurentTranspose_unique
#print axioms StrictEUnit.finiteLogLaurentTranspose_bound_independent
#print axioms StrictEUnit.exists_logPolynomial_iff_uniform_log_bound
#print axioms StrictEUnit.polynomialCoefficientEuler
#print axioms StrictEUnit.polynomialCoefficientEuler_uniform_bound
#print axioms StrictEUnit.finiteLogLaurentTranspose_euler

#print axioms StrictEUnit.uniformLogBound_powerSeries_mk
#print axioms StrictEUnit.finiteLogLaurentTranspose_powerSeries_mk_coeff
