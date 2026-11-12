import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Stage38OrdinarySourceTransport
import Stage53FourierNormalOrdering
import Stage56FiniteFuchs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! SOURCE-ONLY FOCUSED EXTRACTED-SOURCE VALIDATION, UNRUN.
The source partition records every byte. Existing calculus and NormalOrder bodies
are exact checked constituents, not importable exports. Selected Stage57/59/61
bodies are freshly checked here; no blanket acceptance of those modules is claimed.
The separately revised final body uses the same aeval semantics and module action.
The top extension proves the coefficient at ν is 1; full polynomial Monic is not
claimed. No arithmetic regularity, root rationality, splitting or basis is proved.
-/

/-!
SOURCE-ONLY, UNCOMPILED CANDIDATE. This module has only mathlib dependencies.
The first substantive endpoint is logFourier_ordinary_iterate_monomial.
It proves a differential-algebra identity, not an assumed same-operator bridge.
All integer exponent subtraction below is signed subtraction.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The recurrence with its new factor placed on the LEFT, before evaluation
in the generally noncommutative endomorphism algebra. -/
theorem logFourier_shiftedDesc_succ (i : ℤ) (j : ℕ) :
    (descPochhammer K (j + 1)).comp (Polynomial.X + Polynomial.C (i : K)) =
      (Polynomial.X + Polynomial.C ((i : K) - (j : K))) *
        (descPochhammer K j).comp (Polynomial.X + Polynomial.C (i : K)) := by
  rw [descPochhammer_succ_right, Polynomial.mul_comp, Polynomial.sub_comp,
    Polynomial.X_comp, Polynomial.natCast_comp]
  have h : Polynomial.X + Polynomial.C (i : K) - (j : Polynomial K) =
      Polynomial.X + Polynomial.C ((i : K) - (j : K)) := by
    rw [Polynomial.C_sub, Polynomial.C_eq_natCast]
    ring
  rw [h, mul_comm]

/-- A single genuine ordinary differentiation, using the Euler product rule. -/
theorem logFourier_ordinary_monomial_step
    (E : Derivation K A A) (u : ℤ → A)
    (hu : ∀ s t, u (s + t) = u s * u t)
    (hEu : ∀ s, E (u s) = (s : K) • u s) (s : ℤ) (y : A) :
    u (-1) * E (u s * y) = u (s - 1) * (E y + (s : K) • y) := by
  rw [E.leibniz, hEu]
  have hs : s - 1 = -1 + s := by omega
  rw [hs, hu]
  simp only [smul_eq_mul, Algebra.smul_def]
  ring

/-- Exact falling-Pochhammer formula on EVERY element of a commutative
differential algebra. In applications u(s) is the literal z^s, not an
independent operator certificate. No faithfulness assumption is involved. -/
theorem logFourier_ordinary_iterate_monomial
    (E : Derivation K A A) (u : ℤ → A)
    (hu : ∀ s t, u (s + t) = u s * u t)
    (hEu : ∀ s, E (u s) = (s : K) • u s)
    (i : ℤ) (j : ℕ) (y : A) :
    (fun v : A => u (-1) * E v)^[j] (u i * y) =
      u (i - (j : ℤ)) *
        (Polynomial.aeval E.toLinearMap
          ((descPochhammer K j).comp (Polynomial.X + Polynomial.C (i : K)))) y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih,
      logFourier_ordinary_monomial_step E u hu hEu,
      logFourier_shiftedDesc_succ]
    have hs : i - ((j + 1 : ℕ) : ℤ) = (i - (j : ℤ)) - 1 := by omega
    rw [hs]
    simp only [map_mul, map_add, Polynomial.aeval_X, Polynomial.aeval_C,
      Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply,
      Int.cast_sub, Int.cast_natCast]
    rfl

/-- Evaluation at a linear endomorphism is a bounded finite sum of its
actual iterates. Scalar evaluation of a polynomial is not used in its place. -/
theorem logFourier_endomorphism_eval_fin (E : Module.End K A)
    (P : Polynomial K) (n : ℕ) (hP : P.natDegree < n) (y : A) :
    Polynomial.aeval E P y =
      ∑ k : Fin n, P.coeff k.val • (E : A → A)^[k.val] y := by
  rw [Polynomial.aeval_endomorphism,
    Polynomial.sum_over_range' P (f := fun k b => b • (E ^ k) y)
      (fun k => zero_smul K ((E ^ k) y)) n hP]
  simp only [Module.End.pow_apply]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => P.coeff k • (E : A → A)^[k] y) n).symm

/-- The full binomial Leibniz rule for the actual derivation on A. -/
theorem logFourier_iterate_leibniz (d : Derivation K A A) (n : ℕ) (p q : A) :
    (d : A → A)^[n] (p * q) =
      ∑ k ∈ Finset.range n.succ,
        n.choose k • ((d : A → A)^[n-k] p * (d : A → A)^[k] q) := by
  have hd (x y : A) : d (x*y) = d x*y + x*d y := by
    rw [d.leibniz]
    simp only [smul_eq_mul]
    ring
  induction n with
  | zero => simp [Finset.range]
  | succ n ih =>
    calc
      (d : A → A)^[n+1] (p*q) = d
          (∑ k ∈ Finset.range n.succ,
            n.choose k • ((d : A → A)^[n-k] p * (d : A → A)^[k] q)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k+1] p * (d : A → A)^[k] q)) +
          ∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k] p * (d : A → A)^[k+1] q) := by
        simp_rw [map_sum, map_nsmul, hd, Function.iterate_succ_apply',
          smul_add, Finset.sum_add_distrib]
      _ = (∑ k ∈ Finset.range n.succ,
          n.choose k.succ • ((d : A → A)^[n-k] p * (d : A → A)^[k+1] q)) +
          1 • ((d : A → A)^[n+1] p * (d : A → A)^[0] q) +
          ∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k] p * (d : A → A)^[k+1] q) := by
        congr 1
        refine (Finset.sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
        · rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          congr
          omega
        · rw [Nat.choose_zero_right, tsub_zero]
      _ = ((∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k] p * (d : A → A)^[k+1] q)) +
          ∑ k ∈ Finset.range n.succ,
          n.choose k.succ • ((d : A → A)^[n-k] p * (d : A → A)^[k+1] q)) +
          1 • ((d : A → A)^[n+1] p * (d : A → A)^[0] q) := by
        rw [add_comm, add_assoc]
      _ = (∑ k ∈ Finset.range n.succ,
          (n+1).choose (k+1) •
            ((d : A → A)^[n+1-(k+1)] p * (d : A → A)^[k+1] q)) +
          1 • ((d : A → A)^[n+1] p * (d : A → A)^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ,
          add_smul, Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]

/-- A polynomial coefficient in the original coordinate differentiates as
that same polynomial, not as an arbitrary replacement coefficient. -/
theorem logFourier_iterate_aeval (d : Derivation K A A) (z : A)
    (hz : d z = 1) (P : Polynomial K) (n : ℕ) :
    (d : A → A)^[n] (Polynomial.aeval z P) =
      Polynomial.aeval z ((Polynomial.derivative : Polynomial K → Polynomial K)^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.map_aeval, hz,
      smul_eq_mul, mul_one, Function.iterate_succ_apply']

/-- Padded mixed Leibniz rule, with exactly the j-choose-l coefficients used
by Stage53. The finite-log input is unrestricted. -/
theorem logFourier_mixed_leibniz (d : Derivation K A A) (z : A)
    (hz : d z = 1) (P : Polynomial K) (y : A) (ν j : ℕ) (hj : j ≤ ν) :
    (d : A → A)^[j] (Polynomial.aeval z P * y) =
      ∑ l : Fin (ν+1), (j.choose l.val) •
        (Polynomial.aeval z
          ((Polynomial.derivative : Polynomial K → Polynomial K)^[j-l.val] P) *
            (d : A → A)^[l.val] y) := by
  rw [logFourier_iterate_leibniz,
    Fin.sum_univ_eq_sum_range (fun l : ℕ => (j.choose l) •
      (Polynomial.aeval z
        ((Polynomial.derivative : Polynomial K → Polynomial K)^[j-l] P) *
          (d : A → A)^[l] y))]
  simp_rw [logFourier_iterate_aeval d z hz]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hj))
  intro l _ hnot
  have hlt : j < l := by simp only [Finset.mem_range] at hnot; omega
  simp [Nat.choose_eq_zero_of_lt hlt]

end StrictEUnit

end -- close the original calculus anonymous noncomputable section

/-!
SOURCE-ONLY, UNCOMPILED CANDIDATE. All project imports in this module are
baseline modules. It does NOT depend on Stage59 or Stage61 source candidates.
The operators are the actual Stage38 operators on K((t))[ell], for positive
ramification N, with z=t^N and ell unchanged. No new ambient algebra is used.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A literal generic evaluation wrapper: concrete statements need not rebuild
all algebra instances on a large endomorphism type during elaboration. -/
def logFourier_endomorphismEval {F B : Type*} [Field F] [CommRing B] [Algebra F B]
    (E : Module.End F B) (P : Polynomial F) (y : B) : B :=
  Polynomial.aeval E P y

/-- The wrapper is definitionally the same endomorphism evaluation. -/
theorem logFourier_endomorphismEval_eq_aeval
    {F B : Type*} [Field F] [CommRing B] [Algebra F B]
    (E : Module.End F B) (P : Polynomial F) (y : B) :
    logFourier_endomorphismEval E P y = Polynomial.aeval E P y := rfl

variable {K : Type*} [Field K]

-- Align the derivation domain and codomain modules without changing either operator.
-- The coefficientwise module agrees extensionally by stage38_logModule_eq.
attribute [local instance 2000] Algebra.toModule

/-- The constant scalar action expressed in the actual polynomial-log ring. -/
theorem stage61_logScalar_mul (c : K) (y : Polynomial (LaurentSeries K)) :
    c • y = Polynomial.C (HahnSeries.single (0 : ℤ) c) * y := by
  rw [Algebra.smul_def, Polynomial.algebraMap_apply,
    LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

/-- Bundle the existing source Euler function, proving all its laws. -/
def stage61_logEulerDerivation (N : ℕ) :
    Derivation K (Polynomial (LaurentSeries K)) (Polynomial (LaurentSeries K)) where
  toFun := stage38_sourceEuler (K := K) N
  map_add' := stage38_sourceEuler_add (K := K) N
  map_smul' := by
    intro c y
    change stage38_sourceEuler (K := K) N (c • y) =
      c • stage38_sourceEuler (K := K) N y
    rw [Algebra.smul_def, Algebra.smul_def, stage38_sourceEuler_mul,
      stage38_sourceEuler_scalar, mul_zero, add_zero]
  map_one_eq_zero' := by
    change stage38_sourceEuler (K := K) N (1 : Polynomial (LaurentSeries K)) = 0
    simpa only [map_one] using stage38_sourceEuler_scalar (K := K) N (1 : K)
  leibniz' := by
    intro x y
    change stage38_sourceEuler (K := K) N (x * y) =
      x * stage38_sourceEuler (K := K) N y + y * stage38_sourceEuler (K := K) N x
    exact stage38_sourceEuler_mul (K := K) N x y

@[simp] theorem stage61_logEulerDerivation_apply (N : ℕ)
    (y : Polynomial (LaurentSeries K)) :
    stage61_logEulerDerivation N y = stage38_sourceEuler N y := rfl

/-- Bundle the SAME ordinary source function, not a new differentiator. -/
def stage61_logOrdinaryDerivation (N : ℕ) :
    Derivation K (Polynomial (LaurentSeries K)) (Polynomial (LaurentSeries K)) where
  toFun := stage38_sourceOrdinary (K := K) N
  map_add' := stage38_sourceOrdinary_add (K := K) N
  map_smul' := by
    intro c y
    change stage38_sourceOrdinary (K := K) N (c • y) =
      c • stage38_sourceOrdinary (K := K) N y
    simp only [Algebra.smul_def, stage38_sourceOrdinary_apply,
      stage38_sourceEuler_mul, stage38_sourceEuler_scalar, mul_zero, add_zero]
    ring
  map_one_eq_zero' := by
    change Polynomial.C (HahnSeries.single (-(N : ℤ)) (1 : K)) *
      stage61_logEulerDerivation (K := K) N (1 : Polynomial (LaurentSeries K)) = 0
    rw [Derivation.map_one_eq_zero, mul_zero]
  leibniz' := by
    intro x y
    change stage38_sourceOrdinary (K := K) N (x * y) =
      x * stage38_sourceOrdinary (K := K) N y + y * stage38_sourceOrdinary (K := K) N x
    exact stage38_sourceOrdinary_mul (K := K) N x y

@[simp] theorem stage61_logOrdinaryDerivation_apply (N : ℕ)
    (y : Polynomial (LaurentSeries K)) :
    stage61_logOrdinaryDerivation N y = stage38_sourceOrdinary N y := rfl

/-- Literal z^s=t^(N*s), including negative s. -/
def stage61_logZPow (N : ℕ) (s : ℤ) : Polynomial (LaurentSeries K) :=
  Polynomial.C (HahnSeries.single ((N : ℤ) * s) 1)

theorem stage61_logZPow_add (N : ℕ) (s t : ℤ) :
    stage61_logZPow (K := K) N (s+t) =
      stage61_logZPow N s * stage61_logZPow N t := by
  simp only [stage61_logZPow, ← Polynomial.C_mul,
    HahnSeries.single_mul_single, one_mul, mul_add]

@[simp] theorem stage61_logZPow_zero (N : ℕ) : stage61_logZPow (K := K) N 0 = 1 := by
  simp only [stage61_logZPow, mul_zero, HahnSeries.single_zero_one, Polynomial.C_1]

@[simp] theorem stage61_logZPow_one (N : ℕ) :
    stage61_logZPow (K := K) N 1 = stage38_sourceCoordinate N := by
  simp only [stage61_logZPow, stage38_sourceCoordinate, mul_one]

theorem stage61_logCoordinate_pow (N i : ℕ) :
    stage38_sourceCoordinate (K := K) N ^ i = stage61_logZPow N (i : ℤ) := by
  simp only [stage38_sourceCoordinate, stage61_logZPow, ← Polynomial.C_pow,
    HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_comm]

/-- Direct coefficient calculation for the existing normalized Euler operator. -/
theorem stage61_logEuler_monomial (N : ℕ) (a : ℤ) (c : K) :
    stage38_sourceEuler N (Polynomial.C (HahnSeries.single a c)) =
      Polynomial.C (HahnSeries.single a ((a : K) / (N : K) * c)) := by
  have he : laurentEuler (HahnSeries.single a c) =
      HahnSeries.single a ((a : K) * c) := by
    apply HahnSeries.ext
    funext n
    by_cases hn : n = a
    · subst n
      simp only [laurentEuler_coeff, HahnSeries.coeff_single_same]
    · simp only [laurentEuler_coeff, HahnSeries.coeff_single_of_ne hn, mul_zero]
  rw [stage38_sourceEuler_apply, logPolynomialEuler_C, he,
    ← Polynomial.C_mul, HahnSeries.single_mul_single, zero_add]
  apply congrArg Polynomial.C
  apply congrArg (HahnSeries.single a)
  rw [div_eq_mul_inv]
  ring

section CharZero
variable [CharZero K]

theorem stage61_logEuler_ZPow (N : ℕ) (hN : N ≠ 0) (s : ℤ) :
    stage61_logEulerDerivation N (stage61_logZPow (K := K) N s) =
      (s : K) • stage61_logZPow N s := by
  rw [stage61_logEulerDerivation_apply, stage61_logZPow,
    stage61_logEuler_monomial, stage61_logScalar_mul,
    ← Polynomial.C_mul, HahnSeries.single_mul_single, zero_add, mul_one]
  simp only [mul_one]
  have hNk : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  congr 2
  rw [Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ hNk]

theorem stage61_logOrdinary_coordinate (N : ℕ) (hN : N ≠ 0) :
    stage61_logOrdinaryDerivation N (stage38_sourceCoordinate (K := K) N) = 1 := by
  change Polynomial.C (HahnSeries.single (-(N : ℤ)) (1 : K)) *
    stage61_logEulerDerivation N (stage38_sourceCoordinate N) = 1
  have hinv : Polynomial.C (HahnSeries.single (-(N : ℤ)) (1 : K)) =
      stage61_logZPow N (-1) := by
    simp only [stage61_logZPow, mul_neg, mul_one]
  rw [hinv, ← stage61_logZPow_one, stage61_logEuler_ZPow N hN, Int.cast_one,
    Algebra.smul_def, map_one, one_mul, ← stage61_logZPow_add]
  norm_num

/-- Exact ordinary iterate on every polynomial-log input, with the required
falling(T+i,j) and signed monomial exponent i-j. -/
theorem stage61_logOrdinary_iterate_monomial (N : ℕ) (hN : N ≠ 0)
    (i : ℤ) (j : ℕ) (y : Polynomial (LaurentSeries K)) :
    (stage38_sourceOrdinary N)^[j] (stage61_logZPow N i * y) =
      stage61_logZPow N (i - (j : ℤ)) *
        logFourier_endomorphismEval
          ((stage61_logEulerDerivation (K := K) N).toLinearMap :
            Module.End K (Polynomial (LaurentSeries K)))
          ((descPochhammer K j).comp (Polynomial.X + Polynomial.C (i : K))) y := by
  have h := logFourier_ordinary_iterate_monomial
    (K := K) (A := Polynomial (LaurentSeries K))
    (stage61_logEulerDerivation (K := K) N)
    (stage61_logZPow (K := K) N) (stage61_logZPow_add (K := K) N)
    (stage61_logEuler_ZPow (K := K) N hN) i j y
  simpa only [logFourier_endomorphismEval, stage61_logZPow, mul_neg, mul_one,
    stage61_logEulerDerivation_apply, stage38_sourceOrdinary_apply] using h

/-- The actual Fourier tuple acting on finite-log Laurent series. -/
def stage61_logFourierAction {μ ν : ℕ} (N : ℕ)
    (a : Fin (μ+1) → Fin (ν+1) → K) (y : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  ∑ i, ∑ j, Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val * a i j)) *
    (stage38_sourceOrdinary N)^[j.val] (stage61_logZPow N (i.val : ℤ) * y)

/-- Exact Stage53 normal-ordered coefficient tuple acting through Stage38's
ordinary derivation. Its p is fixed to stage53_fourierCoeff a, not selected. -/
def stage61_logNormalOrderAction {μ ν : ℕ} (N : ℕ)
    (a : Fin (μ+1) → Fin (ν+1) → K) (y : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  ∑ l : Fin (ν+1), Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
      (stage53_fourierCoeff a l) * (stage38_sourceOrdinary N)^[l.val] y

/-- Mixed Leibniz in the ACTUAL log ring, with original coordinate z=t^N. -/
theorem stage61_log_mixed_leibniz (N : ℕ) (hN : N ≠ 0) (P : Polynomial K)
    (y : Polynomial (LaurentSeries K)) (ν j : ℕ) (hj : j ≤ ν) :
    (stage38_sourceOrdinary N)^[j]
      (Polynomial.aeval (stage38_sourceCoordinate (K := K) N) P * y) =
      ∑ l : Fin (ν+1), (j.choose l.val) •
        (Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
          ((Polynomial.derivative : Polynomial K → Polynomial K)^[j-l.val] P) *
            (stage38_sourceOrdinary N)^[l.val] y) :=
  logFourier_mixed_leibniz (K := K) (A := Polynomial (LaurentSeries K))
    (stage61_logOrdinaryDerivation (K := K) N)
    (stage38_sourceCoordinate (K := K) N)
    (stage61_logOrdinary_coordinate (K := K) N hN) P y ν j hj

/-- SAME Stage53 p, SAME Fourier tuple, SAME input y, after positive
ramification. This is not obtained by reusing Stage53 on a larger type. -/
theorem stage61_log_fourier_normal_ordering {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (y : Polynomial (LaurentSeries K)) :
    stage61_logFourierAction N a y = stage61_logNormalOrderAction N a y := by
  classical
  have h (i : Fin (μ+1)) (j : Fin (ν+1)) :=
    stage61_log_mixed_leibniz N hN (Polynomial.X^i.val : Polynomial K)
      y ν j.val (by omega)
  simp only [map_pow, Polynomial.aeval_X, stage61_logCoordinate_pow] at h
  unfold stage61_logFourierAction stage61_logNormalOrderAction
  simp_rw [stage53_fourierCoeff_eq_unfiltered, map_sum, Finset.sum_mul,
    map_mul, Polynomial.aeval_C, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (μ+1))))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [nsmul_eq_mul, map_mul, map_natCast,
    Polynomial.algebraMap_apply, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
  simp only [← HahnSeries.C_apply, map_mul]
  ring

end CharZero
end StrictEUnit

end -- close the original normal-order anonymous noncomputable section

-- Exact selected definitions and proofs; no unpinned project imports.
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

def stage57_exponent {μ ν : ℕ} (i : Fin (μ+1)) (j : Fin (ν+1)) : ℤ :=
  (ν : ℤ) - (μ : ℤ) + (i.val : ℤ) - (j.val : ℤ)

def Stage57EulerRegular (p : Polynomial (LaurentSeries K)) : Prop :=
  ∀ k : ℕ, ∀ s : ℤ, s < 0 → (p.coeff k).coeff s = 0

def stage59_regularPart (f : LaurentSeries K) : PowerSeries K :=
  PowerSeries.mk (fun n => f.coeff (n : ℤ))

theorem stage59_ofPowerSeries_regularPart (f : LaurentSeries K)
    (hf : ∀ s : ℤ, s < 0 → f.coeff s = 0) :
    HahnSeries.ofPowerSeries ℤ K (stage59_regularPart f) = f := by
  ext s
  change ((stage59_regularPart f : PowerSeries K) : LaurentSeries K).coeff s = _
  rw [PowerSeries.coeff_coe]
  by_cases hs : s < 0
  · rw [if_pos hs, hf s hs]
  · rw [if_neg hs, stage59_regularPart, PowerSeries.coeff_mk]
    exact congrArg f.coeff (Int.eq_natAbs_of_nonneg (le_of_not_gt hs)).symm

theorem stage59_regular_iff_existsUnique_lift (p : Polynomial (LaurentSeries K)) :
    Stage57EulerRegular p ↔
      ∃! q : Polynomial (PowerSeries K), q.map (HahnSeries.ofPowerSeries ℤ K) = p := by
  constructor
  · intro hr
    have hp : p ∈ Polynomial.lifts (HahnSeries.ofPowerSeries ℤ K) := by
      apply (Polynomial.lifts_iff_coeff_lifts p).mpr
      intro k
      exact ⟨stage59_regularPart (p.coeff k),
        stage59_ofPowerSeries_regularPart (p.coeff k) (hr k)⟩
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts p).mp hp
    refine ⟨q, hq, ?_⟩
    intro r hr
    exact Polynomial.map_injective (HahnSeries.ofPowerSeries ℤ K)
      HahnSeries.ofPowerSeries_injective (hr.trans hq.symm)
  · rintro ⟨q, hq, _⟩ k s hs
    rw [← hq, Polynomial.coeff_map]
    change ((q.coeff k : PowerSeries K) : LaurentSeries K).coeff s = 0
    rw [PowerSeries.coeff_coe, if_pos hs]

def stage59_regularLift (p : Polynomial (LaurentSeries K))
    (hr : Stage57EulerRegular p) : Polynomial (PowerSeries K) :=
  Classical.choose ((stage59_regular_iff_existsUnique_lift p).mp hr).exists

theorem stage59_regularLift_map (p : Polynomial (LaurentSeries K))
    (hr : Stage57EulerRegular p) :
    (stage59_regularLift p hr).map (HahnSeries.ofPowerSeries ℤ K) = p :=
  Classical.choose_spec ((stage59_regular_iff_existsUnique_lift p).mp hr).exists

theorem stage59_regularLift_map_coeff (p : Polynomial (LaurentSeries K))
    (hr : Stage57EulerRegular p) (k : ℕ) :
    HahnSeries.ofPowerSeries ℤ K ((stage59_regularLift p hr).coeff k) = p.coeff k := by
  rw [← Polynomial.coeff_map, stage59_regularLift_map]

def stage61_shiftedDesc (i j : ℕ) : Polynomial K :=
  (descPochhammer K j).comp (Polynomial.X + Polynomial.C (i : K))

theorem stage61_shiftedDesc_natDegree (i j : ℕ) :
    (stage61_shiftedDesc (K := K) i j).natDegree = j := by
  simp only [stage61_shiftedDesc, Polynomial.natDegree_comp,
    descPochhammer_natDegree, Polynomial.natDegree_X_add_C, mul_one]

theorem stage61_shiftedDesc_monic (i j : ℕ) :
    (stage61_shiftedDesc (K := K) i j).Monic :=
  (monic_descPochhammer K j).comp_X_add_C (i : K)

theorem stage61_shiftedDesc_top (i j : ℕ) :
    (stage61_shiftedDesc (K := K) i j).coeff j = 1 := by
  have h := (stage61_shiftedDesc_monic (K := K) i j).coeff_natDegree
  rwa [stage61_shiftedDesc_natDegree] at h

def stage61_fourierCorner {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) : K :=
  (-1 : K)^ν * a (Fin.last μ) (Fin.last ν)

theorem stage61_fourierCorner_ne_zero {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K)
    (hc : a (Fin.last μ) (Fin.last ν) ≠ 0) : stage61_fourierCorner a ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc

def stage61_fourierEulerSymbol {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) : Polynomial (LaurentSeries K) :=
  ∑ i, ∑ j,
    Polynomial.C (HahnSeries.single (stage57_exponent i j) ((-1 : K)^j.val * a i j)) *
      (stage61_shiftedDesc i.val j.val).map (algebraMap K (LaurentSeries K))

theorem stage61_shiftedDesc_map_coeff (i j k : ℕ) :
    ((stage61_shiftedDesc (K := K) i j).map (algebraMap K (LaurentSeries K))).coeff k =
      HahnSeries.single (0 : ℤ) ((stage61_shiftedDesc (K := K) i j).coeff k) := by
  rw [Polynomial.coeff_map, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

theorem stage61_fourierEulerSymbol_coeff {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (k : ℕ) :
    (stage61_fourierEulerSymbol a).coeff k =
      ∑ i, ∑ j, HahnSeries.single (stage57_exponent i j)
        (((-1 : K)^j.val * a i j) * (stage61_shiftedDesc i.val j.val).coeff k) := by
  classical
  simp only [stage61_fourierEulerSymbol, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, stage61_shiftedDesc_map_coeff,
    HahnSeries.single_mul_single, add_zero]

theorem stage61_fourierEulerSymbol_regular {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a) :
    Stage57EulerRegular (stage61_fourierEulerSymbol a) := by
  classical
  intro k s hs
  rw [stage61_fourierEulerSymbol_coeff]
  simp only [HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases he : s = stage57_exponent i j
  · have hij : ν + i.val < j.val + μ := by
      unfold stage57_exponent at he
      omega
    simp only [hf i j hij, mul_zero, zero_mul, map_zero, HahnSeries.coeff_zero]
  · exact HahnSeries.coeff_single_of_ne he

theorem stage61_fourierEulerSymbol_top_column {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) :
    (stage61_fourierEulerSymbol a).coeff ν =
      ∑ i, HahnSeries.single (stage57_exponent i (Fin.last ν))
        ((-1 : K)^ν * a i (Fin.last ν)) := by
  classical
  rw [stage61_fourierEulerSymbol_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (Fin.last ν)]
  · simp only [Fin.val_last, stage61_shiftedDesc_top, mul_one]
  · intro j hj hne
    have hjν : j.val < ν := by
      have hn : j.val ≠ ν := fun h => hne (Fin.ext h)
      omega
    have hd : (stage61_shiftedDesc (K := K) i.val j.val).natDegree < ν := by
      rwa [stage61_shiftedDesc_natDegree]
    simp only [Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero, map_zero]
  · simp

theorem stage61_fourierEulerSymbol_top {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a) :
    (stage61_fourierEulerSymbol a).coeff ν =
      HahnSeries.single (0 : ℤ) (stage61_fourierCorner a) := by
  classical
  rw [stage61_fourierEulerSymbol_top_column, Finset.sum_eq_single (Fin.last μ)]
  · have he : stage57_exponent (Fin.last μ) (Fin.last ν) = 0 := by
      simp only [stage57_exponent, Fin.val_last]
      omega
    rw [he]
    rfl
  · intro i hi hne
    have hiμ : i.val < μ := by
      have hn : i.val ≠ μ := fun h => hne (Fin.ext h)
      omega
    simp only [stage56_fuchs_topColumn a hf i hiμ, mul_zero, map_zero]
  · simp

def stage61_fourierLift {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a) :
    Polynomial (PowerSeries K) :=
  stage59_regularLift (stage61_fourierEulerSymbol a)
    (stage61_fourierEulerSymbol_regular a hf)

theorem stage61_fourierLift_top {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a) :
    (stage61_fourierLift a hf).coeff ν = PowerSeries.C K (stage61_fourierCorner a) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [stage61_fourierLift, stage59_regularLift_map_coeff,
    stage61_fourierEulerSymbol_top a hf, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

def stage61_fourierMonic {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a) :
    Polynomial (PowerSeries K) :=
  Polynomial.C (PowerSeries.C K (stage61_fourierCorner a)⁻¹) * stage61_fourierLift a hf

theorem stage61_fourierMonic_top {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a)
    (hc : a (Fin.last μ) (Fin.last ν) ≠ 0) : (stage61_fourierMonic a hf).coeff ν = 1 := by
  rw [stage61_fourierMonic, Polynomial.coeff_C_mul, stage61_fourierLift_top,
    ← map_mul, inv_mul_cancel₀ (stage61_fourierCorner_ne_zero a hc), map_one]

end StrictEUnit
end -- close the selected-source noncomputable section

/-!
SOURCE-ONLY, UNCOMPILED CANDIDATE. Stage61FourierMonic and its Stage59/57/56
dependencies are separate source-only candidates. They require their own
corrected, coordinated compilation before this module can be validated.

The target is an exact all-input identity in Polynomial (LaurentSeries K),
with N nonzero, D_N=stage38_sourceEuler N and d_z=stage38_sourceOrdinary N.
The same finite tuple a, the literal Stage53 normal-order coefficients, and
the Stage61 monic symbol are retained. No arbitrary annihilator is introduced.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

-- Match the checked concrete derivation/endomorphism module presentation.
-- This is extensionally the same module by stage38_logModule_eq.
attribute [local instance 2000] Algebra.toModule

/-- The literal coefficient map z↦t^N into the unchanged finite-log ring. -/
def stage61_logCoefficientMap (N : ℕ) (hN : N ≠ 0) :
    LaurentSeries K →+* Polynomial (LaurentSeries K) :=
  Polynomial.C.comp (stage38_laurentRamification (K := K) N hN).toRingHom

theorem stage61_logCoefficientMap_monomial (N : ℕ) (hN : N ≠ 0) (s : ℤ) (c : K) :
    stage61_logCoefficientMap N hN (HahnSeries.single s c) =
      Polynomial.C (HahnSeries.single ((N : ℤ)*s) c) := by
  change Polynomial.C (stage38_laurentRamification N hN (HahnSeries.single s c)) = _
  apply congrArg Polynomial.C
  exact HahnSeries.embDomain_single

theorem stage61_logZPow_eq_coefficientMap (N : ℕ) (hN : N ≠ 0) (s : ℤ) :
    stage61_logZPow (K := K) N s =
      stage61_logCoefficientMap N hN (HahnSeries.single s 1) :=
  (stage61_logCoefficientMap_monomial N hN s 1).symm

/-- Stage61's SAME left-normal coefficient list, now acting on actual logs. -/
def stage61_logFourierEulerAction {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (y : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  ∑ k : Fin (ν+1), stage61_logCoefficientMap N hN
      ((stage61_fourierEulerSymbol a).coeff k.val) *
        (stage38_sourceEuler N)^[k.val] y

/-- The fixed same-tuple Fourier term, including its sign, shift, and order.
Unlike the old Laurent-only result, the proof uses the actual log derivative. -/
theorem stage61_normalized_log_fourier_term {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (i : Fin (μ+1)) (j : Fin (ν+1)) (c : K) (y : Polynomial (LaurentSeries K)) :
    stage61_logZPow N ((ν : ℤ)-(μ : ℤ)) *
      (Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val * c)) *
        (stage38_sourceOrdinary N)^[j.val] (stage61_logZPow N (i.val : ℤ) * y)) =
      ∑ k : Fin (ν+1), stage61_logCoefficientMap N hN
        (HahnSeries.single (stage57_exponent i j)
          (((-1 : K)^j.val * c) * (stage61_shiftedDesc i.val j.val).coeff k.val)) *
            (stage38_sourceEuler N)^[k.val] y := by
  classical
  rw [stage61_logOrdinary_iterate_monomial N hN]
  have hs : (descPochhammer K j.val).comp
      (Polynomial.X + Polynomial.C ((i.val : ℤ) : K)) =
      stage61_shiftedDesc (K := K) i.val j.val := by
    simp only [stage61_shiftedDesc, Int.cast_natCast]
  rw [hs, logFourier_endomorphismEval_eq_aeval,
    logFourier_endomorphism_eval_fin (K := K) (A := Polynomial (LaurentSeries K))
      ((stage61_logEulerDerivation (K := K) N).toLinearMap :
        Module.End K (Polynomial (LaurentSeries K)))
      (stage61_shiftedDesc i.val j.val)
      (ν+1) (by rw [stage61_shiftedDesc_natDegree]; exact j.isLt)]
  simp only [Finset.mul_sum, stage61_logScalar_mul]
  apply Finset.sum_congr rfl
  intro k _
  change stage61_logZPow N ((ν : ℤ)-(μ : ℤ)) *
      (Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val*c)) *
        (stage61_logZPow N ((i.val : ℤ)-(j.val : ℤ)) *
          (Polynomial.C (HahnSeries.single (0 : ℤ)
            ((stage61_shiftedDesc i.val j.val).coeff k.val)) *
              (stage38_sourceEuler N)^[k.val] y))) = _
  calc
    _ = (stage61_logZPow N ((ν : ℤ)-(μ : ℤ)) *
        Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val*c)) *
        stage61_logZPow N ((i.val : ℤ)-(j.val : ℤ)) *
        Polynomial.C (HahnSeries.single (0 : ℤ)
          ((stage61_shiftedDesc i.val j.val).coeff k.val))) *
            (stage38_sourceEuler N)^[k.val] y := by ring
    _ = _ := by
      congr 1
      simp only [stage61_logZPow, stage61_logCoefficientMap_monomial,
        ← Polynomial.C_mul, HahnSeries.single_mul_single,
        add_zero, one_mul, mul_one]
      congr 2
      unfold stage57_exponent
      ring

/-- Exact all-input identity BEFORE Fuchs and corner assumptions.
The equality holds on all finite-log inputs, not just ramified Laurent inputs. -/
theorem stage61_same_log_fourier_action {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (y : Polynomial (LaurentSeries K)) :
    stage61_logZPow N ((ν : ℤ)-(μ : ℤ)) * stage61_logFourierAction N a y =
      stage61_logFourierEulerAction N hN a y := by
  classical
  unfold stage61_logFourierAction stage61_logFourierEulerAction
  simp only [Finset.mul_sum, stage61_normalized_log_fourier_term N hN,
    stage61_fourierEulerSymbol_coeff, map_sum, Finset.sum_mul]
  calc
    (∑ i : Fin (μ+1), ∑ j : Fin (ν+1), ∑ k : Fin (ν+1),
      stage61_logCoefficientMap N hN (HahnSeries.single (stage57_exponent i j)
        (((-1 : K)^j.val * a i j) * (stage61_shiftedDesc i.val j.val).coeff k.val)) *
          (stage38_sourceEuler N)^[k.val] y) =
      ∑ i : Fin (μ+1), ∑ k : Fin (ν+1), ∑ j : Fin (ν+1),
      stage61_logCoefficientMap N hN (HahnSeries.single (stage57_exponent i j)
        (((-1 : K)^j.val * a i j) * (stage61_shiftedDesc i.val j.val).coeff k.val)) *
          (stage38_sourceEuler N)^[k.val] y := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- The power-series symbol's left coefficients are embedded and ramified,
while its operator variable is interpreted by genuine D_N iterates. -/
def stage61_logLeftEulerAction (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (p : Polynomial (PowerSeries K)) (y : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  ∑ k : Fin (m+1), stage61_logCoefficientMap N hN
      (HahnSeries.ofPowerSeries ℤ K (p.coeff k.val)) *
        (stage38_sourceEuler N)^[k.val] y

theorem stage61_logLeftEulerAction_C_mul (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (b : PowerSeries K) (p : Polynomial (PowerSeries K))
    (y : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN m (Polynomial.C b*p) y =
      stage61_logCoefficientMap N hN (HahnSeries.ofPowerSeries ℤ K b) *
        stage61_logLeftEulerAction N hN m p y := by
  classical
  simp only [stage61_logLeftEulerAction, Polynomial.coeff_C_mul,
    map_mul, Finset.mul_sum, mul_assoc]

/-- Coefficientwise regular lifting does not alter this same log action. -/
theorem stage61_logFourierLift_action {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a)
    (y : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN ν (stage61_fourierLift a hf) y =
      stage61_logFourierEulerAction N hN a y := by
  classical
  unfold stage61_logLeftEulerAction stage61_logFourierEulerAction
  apply Finset.sum_congr rfl
  intro k _
  rw [stage61_fourierLift, stage59_regularLift_map_coeff]

/-- The exact signed monomial normalization, now for EVERY actual finite-log
input and every positive denominator. The unnormalized tuple is unchanged. -/
theorem stage61_logFourierMonic_action {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a)
    (y : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN ν (stage61_fourierMonic a hf) y =
      Polynomial.C (HahnSeries.single ((N : ℤ)*((ν : ℤ)-(μ : ℤ)))
        (stage61_fourierCorner a)⁻¹) * stage61_logFourierAction N a y := by
  rw [stage61_fourierMonic, stage61_logLeftEulerAction_C_mul,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, stage61_logFourierLift_action,
    ← stage61_same_log_fourier_action N hN,
    stage61_logZPow_eq_coefficientMap N hN,
    ← mul_assoc, ← map_mul, HahnSeries.single_mul_single, zero_add, mul_one,
    stage61_logCoefficientMap_monomial]

/-- Main same-operator endpoint: the literal Stage53 normal-order p and
Stage38 ordinary jets on the SAME actual polynomial-log input y. -/
theorem stage61_logMonic_same_normalOrder_action {μ ν : ℕ} (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a)
    (y : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN ν (stage61_fourierMonic a hf) y =
      Polynomial.C (HahnSeries.single ((N : ℤ)*((ν : ℤ)-(μ : ℤ)))
        (stage61_fourierCorner a)⁻¹) *
      (∑ l : Fin (ν+1), Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
        (stage53_fourierCoeff a l) * (stage38_sourceOrdinary N)^[l.val] y) := by
  rw [stage61_logFourierMonic_action, stage61_log_fourier_normal_ordering N hN]
  rfl

/-- Exact cancellation of the displayed nonzero multiplier. No coefficient
extraction discards log terms and no smaller annihilator is substituted. -/
theorem stage61_logMonic_same_normalOrder_annihilation {μ ν : ℕ}
    (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a)
    (hc : a (Fin.last μ) (Fin.last ν) ≠ 0) (y : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN ν (stage61_fourierMonic a hf) y = 0 ↔
      (∑ l : Fin (ν+1), Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
        (stage53_fourierCoeff a l) * (stage38_sourceOrdinary N)^[l.val] y) = 0 := by
  rw [stage61_logMonic_same_normalOrder_action]
  have hn : (Polynomial.C (HahnSeries.single ((N : ℤ)*((ν : ℤ)-(μ : ℤ)))
      (stage61_fourierCorner a)⁻¹) : Polynomial (LaurentSeries K)) ≠ 0 := by
    intro hz
    have hh := congrArg (fun q : Polynomial (LaurentSeries K) =>
      (q.coeff 0).coeff ((N : ℤ)*((ν : ℤ)-(μ : ℤ)))) hz
    simp only [Polynomial.coeff_C_zero, Polynomial.coeff_zero,
      HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at hh
    exact inv_ne_zero (stage61_fourierCorner_ne_zero a hc) hh
  exact mul_eq_zero.trans (or_iff_right hn)

/-- A named p endpoint records exactly where an existing manuscript tuple
is identified with the literal Fourier normal order. No action equality
appears as a hypothesis; p_l=stage53_fourierCoeff a l is the only p bridge. -/
theorem stage61_logMonic_same_p_annihilation {μ ν : ℕ}
    (N : ℕ) (hN : N ≠ 0)
    (a : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs a)
    (hc : a (Fin.last μ) (Fin.last ν) ≠ 0)
    (p : Fin (ν+1) → Polynomial K) (hp : ∀ l, p l = stage53_fourierCoeff a l)
    (y : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN ν (stage61_fourierMonic a hf) y = 0 ↔
      (∑ l : Fin (ν+1), Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
        (p l) * (stage38_sourceOrdinary N)^[l.val] y) = 0 := by
  simp only [hp]
  exact stage61_logMonic_same_normalOrder_annihilation N hN a hf hc y

end StrictEUnit

end -- close the final normalization anonymous noncomputable section
