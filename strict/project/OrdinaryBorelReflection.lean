import ReverseBorelPolynomialODE
import StrictERescalingArithmetic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Reflection of the literal ordinary Borel input

The formal transport keeps the derivative-order index set and gives the
explicit tuple p_i(-X) * (-1)^i. The signed input is literally the sequence
(-1)^n * a_n. Arithmetic is reused from algebraic rescaling, without claiming
that its original bound or denominator witnesses are retained. No entire
analytic bridge, source regularity, or arithmetic local-basis theorem is used.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

section Formal
variable {K : Type*} [Field K]

/-- Formal rescaling commutes with every derivative iterate with its exact
chain-rule factor. This holds also at scale zero and derivative order zero. -/
theorem ordinaryBorel_rescale_iterate_derivative
    (α : K) (f : PowerSeries K) (i : ℕ) :
    (PowerSeries.derivative K)^[i] (PowerSeries.rescale α f) =
      PowerSeries.C K (α ^ i) *
        PowerSeries.rescale α ((PowerSeries.derivative K)^[i] f) := by
  ext n
  simp only [stage26_coeff_iterate_derivative_asc, PowerSeries.coeff_rescale,
    PowerSeries.coeff_C_mul, pow_add]
  ring

/-- Rescaling of the embedded polynomial is its literal variable substitution. -/
theorem ordinaryBorel_rescale_polynomial (α : K) (p : Polynomial K) :
    PowerSeries.rescale α (p : PowerSeries K) =
      (p.comp (Polynomial.C α * Polynomial.X) : PowerSeries K) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe,
    Polynomial.comp_C_mul_X_coeff]
  exact mul_comm _ _

/-- The explicit reflected coefficient tuple, at exactly the original order. -/
def ordinaryReflectionTuple (m : ℕ) (p : Fin (m + 1) → Polynomial K)
    (i : Fin (m + 1)) : Polynomial K :=
  (p i).comp (-Polynomial.X) * Polynomial.C ((-1 : K) ^ i.val)

/-- A nonzero member of the original tuple stays nonzero after reflection. -/
theorem ordinaryReflectionTuple_nonzero (m : ℕ) (p : Fin (m + 1) → Polynomial K)
    (hp : ∃ i, p i ≠ 0) : ∃ i, ordinaryReflectionTuple m p i ≠ 0 := by
  obtain ⟨i, hi⟩ := hp
  have hcomp : (p i).comp (-Polynomial.X) ≠ 0 := by
    intro h
    apply hi
    have hh := congrArg (fun q : Polynomial K => q.comp (-Polynomial.X)) h
    simpa only [Polynomial.comp_neg_X_comp_neg_X, Polynomial.zero_comp] using hh
  exact ⟨i, mul_ne_zero hcomp
    (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))⟩

/-- Transport the supplied formal equation to the explicit reflected tuple;
no existential replacement operator is used in this statement. -/
theorem ordinaryReflectionTuple_equation (m : ℕ) (p : Fin (m + 1) → Polynomial K)
    (f : PowerSeries K)
    (hode : (∑ i, (p i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] f) = 0) :
    (∑ i, (ordinaryReflectionTuple m p i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] (PowerSeries.rescale (-1 : K) f)) = 0 := by
  have hterm (i : Fin (m + 1)) :
      (ordinaryReflectionTuple m p i : PowerSeries K) *
          (PowerSeries.derivative K)^[i.val] (PowerSeries.rescale (-1 : K) f) =
        PowerSeries.rescale (-1 : K)
          ((p i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] f) := by
    have hpcast : PowerSeries.rescale (-1 : K) (p i : PowerSeries K) =
        ((p i).comp (-Polynomial.X) : PowerSeries K) := by
      simpa only [map_neg, map_one, neg_one_mul] using
        ordinaryBorel_rescale_polynomial (-1 : K) (p i)
    have hsign : (-1 : K) ^ i.val * (-1 : K) ^ i.val = 1 := by
      rw [← mul_pow]
      simp only [neg_mul_neg, one_mul, one_pow]
    rw [ordinaryReflectionTuple, Polynomial.coe_mul, Polynomial.coe_C,
      ordinaryBorel_rescale_iterate_derivative, map_mul, hpcast]
    rw [mul_assoc, ← mul_assoc (PowerSeries.C K ((-1 : K) ^ i.val))
      (PowerSeries.C K ((-1 : K) ^ i.val))
      (PowerSeries.rescale (-1 : K) ((PowerSeries.derivative K)^[i.val] f)),
      ← map_mul, hsign, map_one, one_mul]
  calc
    (∑ i, (ordinaryReflectionTuple m p i : PowerSeries K) *
        (PowerSeries.derivative K)^[i.val] (PowerSeries.rescale (-1 : K) f)) =
        PowerSeries.rescale (-1 : K)
          (∑ i, (p i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] f) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = 0 := by rw [hode, map_zero]

/-- The reflected equation uses the same signed `mk` input required by the
signed inverse-Laplace transform, including the coefficient at zero. -/
theorem ordinaryReflectionTuple_signed_mk (a : ℕ → K)
    (m : ℕ) (p : Fin (m + 1) → Polynomial K)
    (hode : (∑ i, (p i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] (PowerSeries.mk a)) = 0) :
    (∑ i, (ordinaryReflectionTuple m p i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val]
        (PowerSeries.mk (fun n => (-1 : K) ^ n * a n))) = 0 := by
  simpa only [PowerSeries.rescale_mk] using
    ordinaryReflectionTuple_equation m p (PowerSeries.mk a) hode

end Formal

/-- Existing algebraic rescaling gives the full arithmetic predicate for the
signed coefficients. Original certificate witnesses are not asserted equal. -/
theorem strictEArithmetic_signed_coefficients {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    HasStrictEArithmetic (fun n => (-1 : AlgebraicComplex) ^ n * a n) := by
  simpa only [mul_comm] using strictEArithmetic_rescale ha (-1)

/-- The actual Stage41 input supplies both ordinary equations at the SAME
order: the original tuple and its explicitly defined reflection. Arithmetic
belongs to the literal signed coefficients, not a new chosen sequence. -/
theorem stage41_signed_ordinary_borel_data (a : ℕ → AlgebraicComplex)
    (ha : Stage41IsStrictESeries a) :
    HasStrictEArithmetic (fun n => (-1 : AlgebraicComplex) ^ n * a n) ∧
    ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial AlgebraicComplex,
      (∃ i, p i ≠ 0) ∧
      (∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0 ∧
      (∃ i, ordinaryReflectionTuple m p i ≠ 0) ∧
      (∑ i, (ordinaryReflectionTuple m p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val]
          (PowerSeries.mk (fun n => (-1 : AlgebraicComplex) ^ n * a n))) = 0 := by
  obtain ⟨m, p, hp, hode⟩ := stage41_ordinary_borel_polynomial_ode a ha
  exact ⟨strictEArithmetic_signed_coefficients ha.1, m, p, hp, hode,
    ordinaryReflectionTuple_nonzero m p hp,
    ordinaryReflectionTuple_signed_mk a m p hode⟩

end StrictEUnit
end
