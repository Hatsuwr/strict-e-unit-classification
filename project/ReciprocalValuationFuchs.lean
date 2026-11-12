import ReciprocalValuationDegree
import FocusedFourierNormalizationCore

/-! NEW SOURCE-ONLY, UNCOMPILED. Guarded valuations imply the concrete finite
Fuchs condition and corner for the SAME constructed array. Existence of an
operator satisfying these valuation hypotheses remains a separate global gate. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem reciprocalSourcePolynomial_top_natDegree (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0) :
    (reciprocalSourcePolynomial m (reciprocalCommonDegree m q) q m).natDegree =
      reciprocalCommonDegree m q - (q (Fin.last m)).natTrailingDegree + 2*m+1 := by
  have hs : (-1 : K)^m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [reciprocalSourcePolynomial_top,
    Polynomial.natDegree_mul (reciprocalPolynomial_ne_zero _ _ hq)
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hs) (pow_ne_zero _ Polynomial.X_ne_zero)),
    reciprocalReflect_natDegree _ _ (reciprocalCommonDegree_bound m q (Fin.last m)) hq,
    Polynomial.natDegree_C_mul_X_pow _ _ hs]
  omega

theorem reciprocalSourceDegree_of_valuations (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds m q) :
    reciprocalSourceDegree m (reciprocalCommonDegree m q) q =
      reciprocalCommonDegree m q - (q (Fin.last m)).natTrailingDegree + 2*m+1 := by
  apply le_antisymm
  · unfold reciprocalSourceDegree
    apply Finset.sup_le
    intro k hk
    have h := reciprocalSourcePolynomial_natDegree_bound m q hreg k.val
    have hk' := k.isLt
    omega
  · have h := reciprocalSourceDegree_bound m (reciprocalCommonDegree m q) q (Fin.last m)
    change (reciprocalSourcePolynomial m (reciprocalCommonDegree m q) q m).natDegree ≤
      reciprocalSourceDegree m (reciprocalCommonDegree m q) q at h
    rw [reciprocalSourcePolynomial_top_natDegree m q hq] at h
    exact h

theorem reciprocalSourceArray_finiteFuchs (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds m q) :
    Stage56FiniteFuchs (reciprocalSourceArray m (reciprocalCommonDegree m q) q) := by
  intro k j hbad
  change (reciprocalSourcePolynomial m (reciprocalCommonDegree m q) q k.val).coeff j.val = 0
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hb := reciprocalSourcePolynomial_natDegree_bound m q hreg k.val
  have hn := reciprocalSourceDegree_of_valuations m q hq hreg
  change reciprocalSourceDegree m (reciprocalCommonDegree m q) q + k.val < j.val+m at hbad
  omega

theorem reciprocalSourceArray_corner (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds m q) :
    reciprocalSourceArray m (reciprocalCommonDegree m q) q (Fin.last m)
      (Fin.last (reciprocalSourceDegree m (reciprocalCommonDegree m q) q)) =
        (-1 : K)^m * (q (Fin.last m)).coeff (q (Fin.last m)).natTrailingDegree := by
  change (reciprocalSourcePolynomial m (reciprocalCommonDegree m q) q m).coeff
    (reciprocalSourceDegree m (reciprocalCommonDegree m q) q) = _
  rw [reciprocalSourceDegree_of_valuations m q hq hreg,
    ← reciprocalSourcePolynomial_top_natDegree m q hq,
    Polynomial.coeff_natDegree, reciprocalSourcePolynomial_top,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C_mul_X_pow,
    reciprocalReflect_leadingCoeff _ _ (reciprocalCommonDegree_bound m q (Fin.last m)) hq]
  ring

theorem reciprocalSourceArray_corner_ne_zero (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds m q) :
    reciprocalSourceArray m (reciprocalCommonDegree m q) q (Fin.last m)
      (Fin.last (reciprocalSourceDegree m (reciprocalCommonDegree m q) q)) ≠ 0 := by
  rw [reciprocalSourceArray_corner m q hq hreg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq)

/-- Joint output with no newly selected operator or padded-corner assumption. -/
theorem reciprocalSourceArray_fuchs_and_corner (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : q (Fin.last m) ≠ 0)
    (hreg : ∀ i, q i ≠ 0 →
      (q (Fin.last m)).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+m) :
    reciprocalSourceDegree m (reciprocalCommonDegree m q) q =
        reciprocalCommonDegree m q - (q (Fin.last m)).natTrailingDegree + 2*m+1 ∧
      Stage56FiniteFuchs (reciprocalSourceArray m (reciprocalCommonDegree m q) q) ∧
      reciprocalSourceArray m (reciprocalCommonDegree m q) q (Fin.last m)
        (Fin.last (reciprocalSourceDegree m (reciprocalCommonDegree m q) q)) =
          (-1 : K)^m * (q (Fin.last m)).coeff (q (Fin.last m)).natTrailingDegree ∧
      reciprocalSourceArray m (reciprocalCommonDegree m q) q (Fin.last m)
        (Fin.last (reciprocalSourceDegree m (reciprocalCommonDegree m q) q)) ≠ 0 :=
  ⟨reciprocalSourceDegree_of_valuations m q hq hreg,
    reciprocalSourceArray_finiteFuchs m q hq hreg,
    reciprocalSourceArray_corner m q hq hreg,
    reciprocalSourceArray_corner_ne_zero m q hq hreg⟩

end StrictEUnit
end
