import SignedInverseLaplace
import FocusedFourierNormalizationCore

/-! NEW SOURCE-ONLY, UNCOMPILED. Depends on the uncompiled signed transform.
A GIVEN source equation is transported to the exact Stage53 tuple. Neither
source-annihilator existence nor any Fuchs or arithmetic conclusion is asserted. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def signedLaplaceSourceAction {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) : LaurentSeries K :=
  ∑ i, ∑ j, HahnSeries.single (0 : ℤ) (A i j) *
    (fun x : LaurentSeries K => HahnSeries.single (-1 : ℤ) (1 : K) * x)^[j.val]
      ((fun x : LaurentSeries K => HahnSeries.single (2 : ℤ) (-1 : K) *
        laurentOrdinaryDerivation x)^[i.val] y)

theorem signedLaplace_negative_derivative_iterate (f : PowerSeries K) (j : ℕ) :
    (fun x : PowerSeries K => -(PowerSeries.derivative K x))^[j] f =
      PowerSeries.C K ((-1 : K)^j) * (PowerSeries.derivative K)^[j] f := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, map_one, one_mul]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [PowerSeries.derivative_C, mul_zero, add_zero,
      Function.iterate_succ_apply', pow_succ, map_mul, map_neg, map_one]
    ring

theorem signedLaplace_X_iterate (f : PowerSeries K) (i : ℕ) :
    (fun x : PowerSeries K => PowerSeries.X * x)^[i] f = PowerSeries.X^i * f := by
  induction i with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

/-- Coercion is the original-variable polynomial evaluation, not a new scalar action. -/
theorem signedLaplace_aeval_powerSeries (P : Polynomial K) :
    Polynomial.aeval (PowerSeries.X : PowerSeries K) P = (P : PowerSeries K) := by
  change Polynomial.eval₂ (PowerSeries.C K) PowerSeries.X P = _
  exact Polynomial.eval₂_C_X_eq_coe

/-- The generic mixed Leibniz rule gives exactly the Stage53 normal order. -/
theorem signedLaplace_powerSeries_normal_order {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (f : PowerSeries K) :
    (∑ i, ∑ j, PowerSeries.C K ((-1 : K)^j.val * A i j) *
      (PowerSeries.derivative K)^[j.val] (PowerSeries.X^i.val * f)) =
    ∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val] f := by
  have h (i : Fin (μ+1)) (j : Fin (ν+1)) :=
    logFourier_mixed_leibniz (PowerSeries.derivative K)
      (PowerSeries.X : PowerSeries K) (PowerSeries.derivative_X (R := K))
      (Polynomial.X^i.val : Polynomial K) f ν j.val (by omega)
  simp only [signedLaplace_aeval_powerSeries, Polynomial.coe_pow, Polynomial.coe_X] at h
  have hsum {ι : Type} (s : Finset ι) (q : ι → Polynomial K) :
      ((∑ i ∈ s, q i : Polynomial K) : PowerSeries K) =
        ∑ i ∈ s, (q i : PowerSeries K) := by
    exact map_sum Polynomial.coeToPowerSeries.ringHom q s
  simp only [stage53_fourierCoeff_eq_unfiltered, hsum,
    Finset.sum_mul, Polynomial.coe_mul, Polynomial.coe_C, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (μ+1))))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [nsmul_eq_mul, map_mul, map_natCast]
  ring

/-- Exact finite source action under J, with the SAME coefficient array A. -/
theorem signedLaplace_sourceAction {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) :
    signedInverseLaplace (signedLaplaceSourceAction A y) =
      ∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
        (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y) := by
  unfold signedLaplaceSourceAction
  simp_rw [signedInverseLaplace_sum, signedInverseLaplace_constant,
    signedInverseLaplace_z_iterate, signedInverseLaplace_Dz_iterate,
    signedLaplace_negative_derivative_iterate, signedLaplace_X_iterate]
  rw [← signedLaplace_powerSeries_normal_order A (signedInverseLaplace y)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  ring

theorem signedLaplace_same_fourier_kernel {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K)
    (hy : signedLaplaceSourceAction A y = 0) :
    (∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y)) = 0 := by
  rw [← signedLaplace_sourceAction A y, hy, signedInverseLaplace_zero]

/-- Actual signed ordinary Borel input yields the ORIGINAL factorial series,
with the exact Stage53 tuple, rather than an unrelated annihilator. -/
theorem signedLaplace_stage41_same_fourier_kernel {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) (a : ℕ → AlgebraicComplex)
    (hy : signedLaplaceSourceAction A
      (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
        HahnSeries.ofPowerSeries ℤ AlgebraicComplex
          (PowerSeries.mk fun n => (-1 : AlgebraicComplex)^n * a n)) = 0) :
    (∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[l.val] (stage41_strictFormalSeries a)) = 0 := by
  have h := signedLaplace_same_fourier_kernel A _ hy
  rw [signedInverseLaplace_stage41] at h
  exact h

end StrictEUnit
end
