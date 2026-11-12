import FrobeniusIntegralDenominatorStep
import IntegralNormHouse

/-! Convert the algebraic pivot power into an actual positive integer
clearing, using its norm in the SAME containing number field. -/
noncomputable section
open scoped NumberField BigOperators Classical
namespace StrictEUnit

theorem integral_pivot_norm_power_clearing
    (E : IntermediateField ℚ AlgebraicComplex) [NumberField E]
    (v : 𝓞 E) (hv : v≠0) (m : ℕ) :
    ∃ q : ℕ,0<q ∧ q=(Int.natAbs (Algebra.norm ℤ v))^m ∧
      (q : ℝ) ≤ NumberField.house (v : E)^(Module.finrank ℚ E*m) ∧
      ∀ x : AlgebraicComplex,
        IsIntegral ℤ ((((v : E) : AlgebraicComplex)^m)*x) →
        IsIntegral ℤ ((q : AlgebraicComplex)*x) := by
  obtain ⟨hq,hbound,w,hw⟩ := ringOfIntegers_natAbs_norm_certificate v hv
  let q := (Int.natAbs (Algebra.norm ℤ v))^m
  have he : ((Int.natAbs (Algebra.norm ℤ v) : ℕ) : E) = (v : E)*(w : E) := by
    simpa only [map_natCast,map_mul] using congrArg (algebraMap (𝓞 E) E) hw
  have he' : ((Int.natAbs (Algebra.norm ℤ v) : ℕ) : AlgebraicComplex) =
      ((v : E) : AlgebraicComplex)*((w : E) : AlgebraicComplex) := by
    simpa only [map_natCast,map_mul] using congrArg (algebraMap E AlgebraicComplex) he
  refine ⟨q,pow_pos hq _,rfl,?_,?_⟩
  · dsimp only [q]
    rw [Nat.cast_pow,pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbound m
  · intro x hx
    have hwI : IsIntegral ℤ ((w : E) : AlgebraicComplex) :=
      IsIntegral.map (E.val.restrictScalars ℤ) (NumberField.RingOfIntegers.isIntegral_coe w)
    have hI := hx.mul (hwI.pow m)
    convert hI using 1
    dsimp only [q]
    rw [Nat.cast_pow,he',mul_pow]
    ring

end StrictEUnit
end
