import V5ArithmeticNormalization
import V5WideSolutionRelativeBase
import V5SparseArithmeticSeries

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
namespace StrictEUnit

def v5ArithmeticEntirePowerPullback (k : Subfield ℂ) (q : ℕ) (hq : 0 < q)
    (F : subfieldEntireFunctionAlgebra k) : subfieldEntireFunctionAlgebra k := by
  refine ⟨⟨fun z => F.val.val (z^q), F.val.property.comp (differentiable_id.pow q)⟩, ?_⟩
  rw [mem_subfieldEntireFunctionAlgebra]
  intro n
  have hh := v5_entire_power_coefficients_in_range k.subtype hq F.val.val F.val.property
    (fun n => ⟨⟨_, (mem_subfieldEntireFunctionAlgebra k F.val).mp F.property n⟩, rfl⟩) n
  obtain ⟨a, ha⟩ := hh
  exact ha ▸ a.property

theorem V5ArithmeticMeromorphicZero.invCoord (k : Subfield ℂ) :
    V5ArithmeticMeromorphicZero k (fun z : ℂˣ => (↑z⁻¹ : ℂ)) := by
  refine ⟨1, 1, ?_⟩
  intro z
  change 1 = (z : ℂ)^1 * (↑z⁻¹ : ℂ)
  simp

theorem V5ArithmeticMeromorphicZero.pullback {k : Subfield ℂ} {f : ℂˣ → ℂ}
    (h : V5ArithmeticMeromorphicZero k f) {q : ℕ} (hq : 0 < q) :
    V5ArithmeticMeromorphicZero k (fun z => f (z^q)) := by
  obtain ⟨n,F,hF⟩ := h
  refine ⟨q*n, v5ArithmeticEntirePowerPullback k q hq F, ?_⟩
  intro z
  change F.val.val ((z : ℂ)^q) = (z : ℂ)^(q*n) * f (z^q)
  simpa only [Units.val_pow_eq_pow_val, pow_mul] using hF (z^q)

/-- Every member of the actual solution algebra has an arithmetic entire
pole-clearing numerator, provided the original entire generators do. -/
theorem v5_wide_solution_arithmetic_meromorphic_zero {ι : Type}
    (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, f i ∈ subfieldEntireFunctionAlgebra ((algebraicClosure ℚ ℂ).toSubfield))
    (s : v5WideSolutionAlgebra f) :
    V5ArithmeticMeromorphicZero ((algebraicClosure ℚ ℂ).toSubfield) s.val := by
  rcases s with ⟨s, hs⟩
  change s ∈ Algebra.adjoin AlgebraicComplex _ at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i,rfl⟩ | ⟨b,rfl⟩
    · exact V5ArithmeticMeromorphicZero.of_entire ⟨f i, hf i⟩
    · cases b
      · exact V5ArithmeticMeromorphicZero.invCoord _
      · exact V5ArithmeticMeromorphicZero.of_entire (subfieldEntireCoordinate _)
  | algebraMap a =>
    exact V5ArithmeticMeromorphicZero.of_entire
      (algebraMap ((algebraicClosure ℚ ℂ).toSubfield) (subfieldEntireFunctionAlgebra ((algebraicClosure ℚ ℂ).toSubfield)) a)
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | mul x y hx hy ihx ihy => exact ihx.mul ihy

/-- Positive Kummer pullback of any actual solution-algebra element retains
arithmetic finite-pole behavior, not merely complex meromorphy. -/
theorem v5_wide_solution_arithmetic_meromorphic_pullback {ι : Type}
    (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, f i ∈ subfieldEntireFunctionAlgebra ((algebraicClosure ℚ ℂ).toSubfield))
    (s : v5WideSolutionAlgebra f) {q : ℕ} (hq : 0 < q) :
    V5ArithmeticMeromorphicZero ((algebraicClosure ℚ ℂ).toSubfield) (fun z => s.val (z^q)) :=
  (v5_wide_solution_arithmetic_meromorphic_zero f hf s).pullback hq

end StrictEUnit
#print axioms StrictEUnit.V5ArithmeticMeromorphicZero.pullback
#print axioms StrictEUnit.v5_wide_solution_arithmetic_meromorphic_zero
#print axioms StrictEUnit.v5_wide_solution_arithmetic_meromorphic_pullback
