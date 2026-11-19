import ReciprocalSourceEquation
import ReciprocalValuationFuchs

/-! NEW SOURCE-ONLY, UNCOMPILED. Mechanical composition for one GIVEN ordinary
operator with explicit guarded valuations. The reflected Stage41 operator is
not asserted to satisfy those valuations. No full arithmetic family is supplied. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- One exact ordinary tuple determines one reciprocal array and its Fourier
image. Positive Fourier order follows from the proved degree formula. -/
theorem valued_ordinary_ode_reciprocal_fourier (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0)
    (hreg : ∀ i, q i ≠ 0 →
      (q (Fin.last m)).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+m)
    (G : PowerSeries K)
    (hode : (∑ i, (q i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] G) = 0) :
    let d := reciprocalCommonDegree m q
    let ν := reciprocalSourceDegree m d q
    let A := reciprocalSourceArray m d q
    let y := HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K G
    0 < ν ∧ Stage56FiniteFuchs A ∧ A (Fin.last m) (Fin.last ν) ≠ 0 ∧
      signedLaplaceSourceAction A y = 0 ∧
      (∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
        (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y)) = 0 := by
  have hν := reciprocalSourceDegree_of_valuations m q hq hreg
  have hpos : 0 < reciprocalSourceDegree m (reciprocalCommonDegree m q) q := by
    omega
  have hsource := ordinaryODE_nonzero_reciprocal_source m q ⟨Fin.last m, hq⟩ G hode
  refine ⟨hpos, reciprocalSourceArray_finiteFuchs m q hq hreg,
    reciprocalSourceArray_corner_ne_zero m q hq hreg, hsource.2, ?_⟩
  exact signedLaplace_same_fourier_kernel _ _ hsource.2

/-- Original factorial coefficients are retained only for the exact signed mk
input shown here. q is the SAME supplied tuple, not a newly selected operator. -/
theorem valued_signed_ordinary_original_factorial (m : ℕ)
    (q : Fin (m+1) → Polynomial AlgebraicComplex) (hq : q (Fin.last m) ≠ 0)
    (hreg : ∀ i, q i ≠ 0 →
      (q (Fin.last m)).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+m)
    (a : ℕ → AlgebraicComplex)
    (hode : (∑ i, (q i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val]
        (PowerSeries.mk fun n => (-1 : AlgebraicComplex)^n * a n)) = 0) :
    let d := reciprocalCommonDegree m q
    let ν := reciprocalSourceDegree m d q
    let A := reciprocalSourceArray m d q
    0 < ν ∧ Stage56FiniteFuchs A ∧ A (Fin.last m) (Fin.last ν) ≠ 0 ∧
      signedLaplaceSourceAction A
        (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
          HahnSeries.ofPowerSeries ℤ AlgebraicComplex
            (PowerSeries.mk fun n => (-1 : AlgebraicComplex)^n * a n)) = 0 ∧
      (∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[l.val] (stage41_strictFormalSeries a)) = 0 := by
  have h := valued_ordinary_ode_reciprocal_fourier m q hq hreg
    (PowerSeries.mk fun n => (-1 : AlgebraicComplex)^n * a n) hode
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  exact signedLaplace_stage41_same_fourier_kernel _ a h.2.2.2.1

end StrictEUnit
end
