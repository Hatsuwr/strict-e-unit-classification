import OrdinaryBorelReflection
import ReciprocalValuationDegree

/-! NEW SOURCE-ONLY, UNCOMPILED. Exact reflection preserves coefficient
support, trailing degrees, and the guarded regular-singular inequalities.
This proves sign invariance, not existence of an operator with those bounds. -/
noncomputable section
open scoped Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem ordinaryReflectionTuple_coeff (m : ℕ) (p : Fin (m+1) → Polynomial K)
    (i : Fin (m+1)) (n : ℕ) :
    (ordinaryReflectionTuple m p i).coeff n = (p i).coeff n * (-1 : K)^(n+i.val) := by
  have hneg : -(Polynomial.X : Polynomial K) = Polynomial.C (-1 : K) * Polynomial.X := by
    simp only [map_neg, map_one, neg_one_mul]
  rw [ordinaryReflectionTuple, Polynomial.coeff_mul_C, hneg,
    Polynomial.comp_C_mul_X_coeff, pow_add]
  ring

theorem ordinaryReflectionTuple_ne_zero_iff (m : ℕ)
    (p : Fin (m+1) → Polynomial K) (i : Fin (m+1)) :
    ordinaryReflectionTuple m p i ≠ 0 ↔ p i ≠ 0 := by
  constructor
  · intro h hp
    apply h
    simp only [ordinaryReflectionTuple, hp, Polynomial.zero_comp, zero_mul]
  · intro hp hzero
    apply hp
    ext n
    have h := congrArg (fun q : Polynomial K => q.coeff n) hzero
    dsimp only at h
    rw [ordinaryReflectionTuple_coeff, Polynomial.coeff_zero] at h
    exact (mul_eq_zero.mp h).resolve_right
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

theorem ordinaryReflectionTuple_natTrailingDegree (m : ℕ)
    (p : Fin (m+1) → Polynomial K) (i : Fin (m+1)) :
    (ordinaryReflectionTuple m p i).natTrailingDegree = (p i).natTrailingDegree := by
  have hs : (ordinaryReflectionTuple m p i).support = (p i).support := by
    ext n
    have hsign : (-1 : K)^(n+i.val) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    simp only [Polynomial.mem_support_iff, ordinaryReflectionTuple_coeff, mul_ne_zero_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hsign⟩⟩
  unfold Polynomial.natTrailingDegree Polynomial.trailingDegree
  rw [hs]

/-- Same index/order, same true-last condition, and exactly the original
zero-guarded inequalities. Neither side is asserted to exist automatically. -/
theorem ordinaryReflectionTuple_last_and_valuation_iff (m : ℕ)
    (p : Fin (m+1) → Polynomial K) :
    ((ordinaryReflectionTuple m p (Fin.last m) ≠ 0) ∧
      ReciprocalRegularSingularBounds m (ordinaryReflectionTuple m p)) ↔
    ((p (Fin.last m) ≠ 0) ∧ ReciprocalRegularSingularBounds m p) := by
  simp only [ReciprocalRegularSingularBounds, ordinaryReflectionTuple_ne_zero_iff,
    ordinaryReflectionTuple_natTrailingDegree]

end StrictEUnit
end
