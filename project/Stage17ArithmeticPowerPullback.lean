import Stage14ActualAnalyticODETransfer
import FormalAmbientDifferentialField

/-!
# Actual arithmetic power pullback

The function is composed with the actual complex power map. Its genuine Cauchy
coefficients are computed by reindexing its convergent Taylor sum. No arbitrary
formal series is asserted to converge, and strict-E closure under ramification
is not asserted.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

/-- Actual entire composition with the positive power map. -/
def stage17_entirePowerPullback (N : ℕ) : entireFunctionAlgebra →ₐ[ℂ] entireFunctionAlgebra where
  toFun f := ⟨fun z => f.val (z ^ N), f.property.comp (differentiable_id.pow N)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem stage17_entirePowerPullback_apply (N : ℕ)
    (f : entireFunctionAlgebra) (z : ℂ) :
    (stage17_entirePowerPullback N f).val z = f.val (z ^ N) := rfl

/-- Exact coefficient formula: pullback inserts zeros outside multiples of N. -/
theorem stage17_entirePowerPullback_coefficient (N : ℕ) (hN : N ≠ 0)
    (f : entireFunctionAlgebra) (j : ℕ) :
    entireCauchyCoefficient (fun z => f.val (z ^ N)) j =
      if N ∣ j then entireCauchyCoefficient f.val (j / N) else 0 := by
  apply entireCauchyCoefficient_eq_of_hasSum
    (f.property.comp (differentiable_id.pow N))
  intro z
  have hinj : Function.Injective (fun i : ℕ => N * i) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) hij
  apply (hinj.hasSum_iff ?_).mp
  · change HasSum (fun i => (if N ∣ N * i then
        entireCauchyCoefficient f.val (N * i / N) else 0) * z ^ (N * i)) (f.val (z ^ N))
    simpa only [dvd_mul_right, if_true, Nat.mul_div_right _
      (Nat.pos_of_ne_zero hN), pow_mul] using entireCauchyCoefficient_hasSum f.property (z ^ N)
  · intro j hj
    have hnd : ¬ N ∣ j := by
      rintro ⟨i, hi⟩
      exact hj ⟨i, hi.symm⟩
    simp only [if_neg hnd, zero_mul]

/-- Arithmetic Taylor coefficient membership survives actual power pullback. -/
theorem stage17_entirePowerPullback_mem (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) :
    stage17_entirePowerPullback N f.val ∈ subfieldEntireFunctionAlgebra k := by
  rw [mem_subfieldEntireFunctionAlgebra]
  intro j
  change entireCauchyCoefficient (fun z => f.val.val (z ^ N)) j ∈ k
  rw [stage17_entirePowerPullback_coefficient N hN]
  split_ifs
  · exact (mem_subfieldEntireFunctionAlgebra k f.val).mp f.property _
  · exact k.zero_mem

/-- Power pullback as a genuine homomorphism of actual arithmetic entire functions. -/
def stage17_arithmeticPowerPullback (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0) :
    subfieldEntireFunctionAlgebra k →ₐ[k] subfieldEntireFunctionAlgebra k where
  toFun f := ⟨stage17_entirePowerPullback N f.val,
    stage17_entirePowerPullback_mem k N hN f⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem stage17_arithmeticPowerPullback_apply (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (f : subfieldEntireFunctionAlgebra k) (z : ℂ) :
    (stage17_arithmeticPowerPullback k N hN f).val.val z = f.val.val (z ^ N) := rfl

/-- The chain rule in Euler normalization, stated for actual entire functions. -/
theorem stage17_arithmeticPowerPullback_euler (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (f : subfieldEntireFunctionAlgebra k) :
    subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k
      (stage17_arithmeticPowerPullback k N hN f) =
      (N : subfieldEntireFunctionAlgebra k) * stage17_arithmeticPowerPullback k N hN
        (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  change z * deriv (fun w => f.val.val (w ^ N)) z =
    (N : ℂ) * (z ^ N * deriv f.val.val (z ^ N))
  have hd : deriv (fun w => f.val.val (w ^ N)) z =
      deriv f.val.val (z ^ N) * ((N : ℂ) * z ^ (N - 1)) :=
    ((f.val.property (z ^ N)).hasDerivAt.comp z (hasDerivAt_pow N z)).deriv
  rw [hd]
  have hp : z * z ^ (N - 1) = z ^ N := by
    rw [← pow_succ']
    congr 1
    omega
  calc
    _ = (N : ℂ) * (z * z ^ (N - 1)) * deriv f.val.val (z ^ N) := by ring
    _ = _ := by rw [hp]; ring

/-- At the normalized point one, power pullback leaves the value unchanged. -/
@[simp] theorem stage17_arithmeticPowerPullback_at_one (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (f : subfieldEntireFunctionAlgebra k) :
    (stage17_arithmeticPowerPullback k N hN f).val.val 1 = f.val.val 1 := by
  simp only [stage17_arithmeticPowerPullback_apply, one_pow]

end StrictEUnit
