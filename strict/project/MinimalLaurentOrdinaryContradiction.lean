import OrdinaryBorelMinimalCyclic
import OrdinaryPolynomialLaurentNoPole
import FormalFundamentalMatrix

/-!
NEW PROOF RECONSTRUCTION, not a recovered source body.

An independent rational differential system transfers scalar annihilators by
universal coefficient rows. Apply this to the actual minimal derivative system
and the normalized formal fundamental matrix at one. The supplied annihilator
of (X-1)⁻¹ F would make t⁻¹ times the normalized first solution pole-free, which
contradicts that solution's initial value one.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit

private def contradictionRowStep {K : Type*} [Field K] {r : ℕ}
    (A : Fin r → Fin r → RatFunc K) (q : Fin r → RatFunc K) : Fin r → RatFunc K :=
  fun j => stage14_rationalOrdinaryDerivation (q j) + ∑ i, q i * A i j

/-- Universal coefficient differentiation uses an explicit rational embedding.
This avoids identifying the standard and translated scalar actions. -/
private theorem contradictionRowStep_eval
    {K : Type*} [Field K] {r : ℕ}
    (φ : RatFunc K →+* LaurentSeries K)
    (hφ : ∀ c, laurentOrdinaryDerivation (φ c) =
      φ (stage14_rationalOrdinaryDerivation c))
    (A : Fin r → Fin r → RatFunc K) (Y : Fin r → LaurentSeries K)
    (hY : ∀ i, laurentOrdinaryDerivation (Y i) = ∑ j, φ (A i j) * Y j)
    (q : Fin r → RatFunc K) :
    laurentOrdinaryDerivation (∑ j, φ (q j) * Y j) =
      ∑ j, φ (contradictionRowStep A q j) * Y j := by
  classical
  calc
    _ = ∑ i, (φ (stage14_rationalOrdinaryDerivation (q i)) * Y i +
        ∑ j, φ (q i * A i j) * Y j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Derivation.leibniz, hφ, hY]
      simp only [smul_eq_mul, Finset.mul_sum, map_mul]
      rw [add_comm]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [contradictionRowStep, map_add, map_sum, add_mul,
        Finset.sum_mul, Finset.sum_add_distrib]

private theorem contradictionRowIterate_eval
    {K : Type*} [Field K] {r : ℕ}
    (φ : RatFunc K →+* LaurentSeries K)
    (hφ : ∀ c, laurentOrdinaryDerivation (φ c) =
      φ (stage14_rationalOrdinaryDerivation c))
    (A : Fin r → Fin r → RatFunc K) (Y : Fin r → LaurentSeries K)
    (hY : ∀ i, laurentOrdinaryDerivation (Y i) = ∑ j, φ (A i j) * Y j)
    (q : Fin r → RatFunc K) (n : ℕ) :
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[n]
        (∑ j, φ (q j) * Y j) =
      ∑ j, φ ((contradictionRowStep A)^[n] q j) * Y j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, contradictionRowStep_eval φ hφ A Y hY,
      Function.iterate_succ_apply']

private theorem contradictionRowCombination_eval
    {K : Type*} [Field K] {r s : ℕ}
    (φ : RatFunc K →+* LaurentSeries K)
    (q : Fin s → Fin r → RatFunc K) (c : Fin s → RatFunc K)
    (Y : Fin r → LaurentSeries K) :
    (∑ i, φ (c i) * ∑ j, φ (q i j) * Y j) =
      ∑ j, φ (∑ i, c i * q i j) * Y j := by
  simp only [Finset.mul_sum, map_sum, map_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- Every annihilator of a scaled coordinate of a rationally independent
system transfers to every solution of that same system under an explicit
compatible rational embedding. This is proved from coefficient rows, not
assumed as a target-specific transport principle. -/
private theorem contradiction_scaled_system_transfer
    {K : Type*} [Field K] {r : ℕ}
    (ψ : RatFunc K →+* LaurentSeries K)
    (hψ : ∀ c, laurentOrdinaryDerivation (ψ c) =
      ψ (stage14_rationalOrdinaryDerivation c))
    (A : Fin r → Fin r → RatFunc K)
    (F Y : Fin r → LaurentSeries K)
    (hli : LinearIndependent (RatFunc K) F)
    (hF : ∀ i, laurentOrdinaryDerivation (F i) =
      ∑ j, algebraMap (RatFunc K) (LaurentSeries K) (A i j) * F j)
    (hY : ∀ i, laurentOrdinaryDerivation (Y i) = ∑ j, ψ (A i j) * Y j)
    (i₀ : Fin r) (a : RatFunc K) (m : ℕ) (c : Fin (m+1) → RatFunc K)
    (hann : (∑ i, algebraMap (RatFunc K) (LaurentSeries K) (c i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (algebraMap (RatFunc K) (LaurentSeries K) a * F i₀)) = 0) :
    (∑ i, ψ (c i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (ψ a * Y i₀)) = 0 := by
  classical
  let φ : RatFunc K →+* LaurentSeries K := algebraMap (RatFunc K) (LaurentSeries K)
  let q : Fin r → RatFunc K := Pi.single i₀ a
  let rows : Fin (m+1) → Fin r → RatFunc K :=
    fun i => (contradictionRowStep A)^[i.val] q
  let Q : Fin r → RatFunc K := fun j => ∑ i, c i * rows i j
  have hsingle (η : RatFunc K →+* LaurentSeries K) (Z : Fin r → LaurentSeries K) :
      (∑ j, η (q j) * Z j) = η a * Z i₀ := by
    rw [Finset.sum_eq_single i₀]
    · simp [q]
    · intro j _ hj
      simp [q, Pi.single_apply, hj, Ne.symm hj]
    · simp
  have hiterF (i : Fin (m+1)) :
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (φ a * F i₀) = ∑ j, φ (rows i j) * F j := by
    rw [← hsingle φ F]
    exact contradictionRowIterate_eval φ stage14_rationalLaurent_differential A F hF q i.val
  have hiterY (i : Fin (m+1)) :
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (ψ a * Y i₀) = ∑ j, ψ (rows i j) * Y j := by
    rw [← hsingle ψ Y]
    exact contradictionRowIterate_eval ψ hψ A Y hY q i.val
  have hQF : (∑ j, φ (Q j) * F j) = 0 := by
    change (∑ i, φ (c i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (φ a * F i₀)) = 0 at hann
    simp_rw [hiterF] at hann
    exact (contradictionRowCombination_eval φ rows c F).symm.trans hann
  have hQ : ∀ j, Q j = 0 := by
    apply (Fintype.linearIndependent_iff.1 hli) Q
    simpa only [Algebra.smul_def] using hQF
  simp_rw [hiterY]
  rw [contradictionRowCombination_eval ψ rows c Y]
  change (∑ j, ψ (Q j) * Y j) = 0
  simp only [hQ, map_zero, zero_mul, Finset.sum_const_zero]

/-- The actual minimal recurrence cannot be ordinary at one if dividing its
source by X-1 gives a solution of a polynomial equation ordinary there.
The conclusion uses precisely the caller's Laurent sources and hypotheses. -/
theorem minimal_laurent_recurrence_not_regular_at_one
    {K : Type*} [Field K] [CharZero K]
    (F G : LaurentSeries K) (r : ℕ) (hr : 0 < r)
    (b : Fin r → RatFunc K) (hmin : OrdinaryBorelMinimalCyclicData F r b)
    (hmul : algebraMap (Polynomial K) (LaurentSeries K)
      (Polynomial.X - Polynomial.C 1) * G = F)
    (m : ℕ) (p : Fin (m+1) → Polynomial K)
    (hord : (p (Fin.last m)).eval 1 ≠ 0)
    (hann : (∑ i, algebraMap (Polynomial K) (LaurentSeries K) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G) = 0) :
    ¬ (∀ i, ∃ B : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K B = ordinaryPointRationalMap 1 (b i)) := by
  classical
  intro hreg
  choose B hB using hreg
  let Φ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  let ψ : RatFunc K →+* LaurentSeries K := ordinaryPointRationalMap 1
  let A : Fin r → Fin r → RatFunc K := minimalDerivativeCompanion r b
  let C : Matrix (Fin r) (Fin r) (PowerSeries K) := fun i j =>
    if i.val + 1 < r then (if j.val = i.val + 1 then 1 else 0) else B j
  let W := formalFundamentalMatrix C
  let i₀ : Fin r := ⟨0, hr⟩
  let Y : Fin r → LaurentSeries K := fun i => Φ (W i i₀)
  let v : Fin r → LaurentSeries K := fun i =>
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] F
  have hC (i j : Fin r) : Φ (C i j) = ψ (A i j) := by
    by_cases hi : i.val + 1 < r
    · by_cases hj : j.val = i.val + 1
      · simp [C, A, minimalDerivativeCompanion, hi, hj, Φ, ψ]
      · simp [C, A, minimalDerivativeCompanion, hi, hj, Φ, ψ]
    · simpa only [C, A, minimalDerivativeCompanion, if_neg hi] using hB j
  have hW (i : Fin r) : PowerSeries.derivative K (W i i₀) =
      ∑ j, C i j * W j i₀ := by
    exact congrArg (fun Z : Matrix (Fin r) (Fin r) (PowerSeries K) => Z i i₀)
      (formalFundamentalMatrix_derivative C)
  have hY (i : Fin r) : laurentOrdinaryDerivation (Y i) =
      ∑ j, ψ (A i j) * Y j := by
    change laurentOrdinaryDerivation (Φ (W i i₀)) = _
    rw [laurentOrdinaryDerivation_ofPowerSeries, hW, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change Φ (C i j * W j i₀) = ψ (A i j) * Φ (W j i₀)
    rw [map_mul, hC]
  have hv (i : Fin r) : laurentOrdinaryDerivation (v i) =
      ∑ j, algebraMap (RatFunc K) (LaurentSeries K) (A i j) * v j := by
    simpa only [Algebra.smul_def] using hmin.2.2.2.2 i
  let t : Polynomial K := Polynomial.X - Polynomial.C 1
  let a : RatFunc K := (algebraMap (Polynomial K) (RatFunc K) t)⁻¹
  let c : Fin (m+1) → RatFunc K := fun i =>
    algebraMap (Polynomial K) (RatFunc K) (p i)
  have hpoly (P : Polynomial K) :
      algebraMap (RatFunc K) (LaurentSeries K)
        (algebraMap (Polynomial K) (RatFunc K) P) =
      algebraMap (Polynomial K) (LaurentSeries K) P := by
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
  have ht : t ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (0 : K)) h
    simp [t] at he
  have htL : algebraMap (Polynomial K) (LaurentSeries K) t ≠ 0 := by
    intro h
    apply ht
    exact (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K))
      (h.trans (map_zero _).symm)
  have haF : algebraMap (RatFunc K) (LaurentSeries K) a * v i₀ = G := by
    change algebraMap (RatFunc K) (LaurentSeries K)
      ((algebraMap (Polynomial K) (RatFunc K) t)⁻¹) * F = G
    rw [map_inv₀, hpoly, ← hmul]
    change (algebraMap (Polynomial K) (LaurentSeries K) t)⁻¹ *
      (algebraMap (Polynomial K) (LaurentSeries K) t * G) = G
    rw [← mul_assoc, inv_mul_cancel₀ htL, one_mul]
  have hsource : (∑ i, algebraMap (RatFunc K) (LaurentSeries K) (c i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (algebraMap (RatFunc K) (LaurentSeries K) a * v i₀)) = 0 := by
    simpa only [c, hpoly, haF] using hann
  have htarget := contradiction_scaled_system_transfer ψ
    (ordinaryPointRationalMap_derivative 1) A v Y hmin.1 hv hY i₀ a m c hsource
  have hat : ψ a = (Φ PowerSeries.X)⁻¹ := by
    change ordinaryPointRationalMap 1
      ((algebraMap (Polynomial K) (RatFunc K) t)⁻¹) = _
    rw [map_inv₀, ordinaryPointRationalMap_polynomial]
    congr 1
    change algebraMap (Polynomial K) (LaurentSeries K)
      (ordinaryPointPolynomialShift 1 t) = Φ PowerSeries.X
    have hshift : ordinaryPointPolynomialShift 1 t = Polynomial.X := by
      simp [t, ordinaryPointPolynomialShift_apply, Polynomial.sub_comp]
    rw [hshift, Polynomial.algebraMap_hahnSeries_apply]
    rw [Polynomial.coe_X]
  have htarget' : (∑ i, ordinaryPointPolynomialMap 1 (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        ((Φ PowerSeries.X)⁻¹ * Φ (W i₀ i₀))) = 0 := by
    simpa only [c, ψ, ordinaryPointRationalMap_polynomial, hat, Y] using htarget
  obtain ⟨w, hw⟩ := ordinaryPoint_polynomial_relation_powerSeries (1 : K) m p hord
    ((Φ PowerSeries.X)⁻¹ * Φ (W i₀ i₀)) htarget'
  have hx : Φ PowerSeries.X ≠ 0 := by
    intro h
    exact PowerSeries.X_ne_zero
      (HahnSeries.ofPowerSeries_injective (h.trans (map_zero Φ).symm))
  have hpower : PowerSeries.X * w = W i₀ i₀ := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [map_mul, hw, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  have hzero : PowerSeries.constantCoeff K (W i₀ i₀) = 0 := by
    have h := congrArg (PowerSeries.constantCoeff K) hpower
    simpa only [map_mul, PowerSeries.constantCoeff_X, zero_mul] using h.symm
  have hone : PowerSeries.constantCoeff K (W i₀ i₀) = 1 := by
    have h := congrArg (fun Z : Matrix (Fin r) (Fin r) K => Z i₀ i₀)
      (formalFundamentalMatrix_constantCoeff C)
    simpa only [Matrix.map_apply, Matrix.one_apply_eq] using h
  exact zero_ne_one (hzero.symm.trans hone)

end StrictEUnit
