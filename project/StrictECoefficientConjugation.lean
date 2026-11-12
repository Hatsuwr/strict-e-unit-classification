import Stage41StrictSeriesCorrespondence
import SelectedScalarFieldMapTransport
import Stage14StrictERingClosure
import AlgebraicScalarExponential

/-! Conjugate actual strict-E functions are reconstructed from conjugate
factorial coefficients. No automorphism is applied to arbitrary complex values. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem strictEArithmetic_map
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex)
    {a : ℕ → AlgebraicComplex} (ha : HasStrictEArithmetic a) :
    HasStrictEArithmetic (fun n => σ (a n)) := by
  obtain ⟨C, hC, hconj, d, hd, hdb, hint⟩ := ha
  let v : AlgebraicComplex →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val
  refine ⟨C, hC, ?_, d, hd, hdb, ?_⟩
  · intro τ n
    simpa only [AlgHom.comp_apply] using hconj (τ.comp σ) n
  · intro n j hj
    have hi : IsIntegral ℤ ((d n : AlgebraicComplex) * a j) := by
      apply (isIntegral_algHom_iff (v.restrictScalars ℤ) v.injective).mp
      simpa only [map_mul, map_natCast] using hint n j hj
    have hm := IsIntegral.map ((v.comp σ).restrictScalars ℤ) hi
    simpa only [map_mul, map_natCast, AlgHom.comp_apply] using hm

theorem stage41_strictFormalSeries_map
    (σ : AlgebraicComplex →+* AlgebraicComplex) (a : ℕ → AlgebraicComplex) :
    PowerSeries.map σ (stage41_strictFormalSeries a) =
      stage41_strictFormalSeries (fun n => σ (a n)) := by
  ext n
  simp only [PowerSeries.coeff_map, stage41_coeff_strictFormalSeries, map_div₀, map_natCast]

theorem stage41_strictSeries_coefficient_map
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex)
    {a : ℕ → AlgebraicComplex} (ha : Stage41IsStrictESeries a) :
    Stage41IsStrictESeries (fun n => σ (a n)) := by
  obtain ⟨harith, m, p, ⟨i, hi⟩, hode⟩ := ha
  refine ⟨strictEArithmetic_map σ harith, m, (fun j => (p j).map σ.toRingHom),
    ⟨i, (Polynomial.map_ne_zero_iff σ.injective).2 hi⟩, ?_⟩
  have hm := ordinaryTuple_equation_map σ.toRingHom m p (stage41_strictFormalSeries a) hode
  simpa only [stage41_strictFormalSeries_map] using hm

theorem actualStrictE_coefficient_conjugate
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex)
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z^n / (n.factorial : ℂ)) (f z)) :
    IsStrictEFunction (stage41_strictSeriesFunction (fun n => σ (a n))) :=
  stage41_strictSeries_isStrictEFunction
    (stage41_strictSeries_coefficient_map σ (stage41_actualStrictE_isStrictESeries hf a hs))

theorem strictEFunction_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsStrictEFunction (f i)) :
    IsStrictEFunction (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using algebraic_constant_isStrictEFunction (1 : AlgebraicComplex)
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using strictEFunction_mul (hf i (Finset.mem_insert_self i s)) hs
end StrictEUnit
