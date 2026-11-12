import ActualMinimalArithmeticConnection

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

/-- Original input only: one Stage41 field/ODE/minimal-companion witness is
chosen and retained. No supplied rank, small denominator, or system premise. -/
theorem stage41_same_input_arithmetic_minimal_connection
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ m : ℕ, ∃ q : Fin (m+1) → Polynomial AlgebraicComplex,
      ∃ F : IntermediateField ℚ AlgebraicComplex,
      ∃ hmem : ∀ n, a n ∈ F, ∃ qF : Fin (m+1) → Polynomial F,
        FiniteDimensional ℚ F ∧
        (∀ i, (qF i).map (algebraMap F AlgebraicComplex) = q i) ∧
        (∃ i, q i ≠ 0) ∧ (∃ i, qF i ≠ 0) ∧
        (∑ i, algebraMap (Polynomial F) (LaurentSeries F) (qF i) *
          (laurentOrdinaryDerivation : LaurentSeries F → LaurentSeries F)^[i.val]
            (HahnSeries.ofPowerSeries ℤ F
              (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)))) = 0 ∧
        (∃ hNF : NumberField F, ∃ r, 0 < r ∧ ∃ c : Fin r → RatFunc F,
          @OrdinaryBorelArithmeticConnectionData F _ hNF
            (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) r c) ∧
        HasStrictEArithmetic a := by
  obtain ⟨m,q,F,hmem,qF,hfinite,hmap,hq,hqF,hode,hminimal,harith⟩ :=
    stage41_ordinary_borel_same_input_polynomial_connection a ha hne
  obtain ⟨r,hr,c,hdata⟩ := hminimal
  letI : FiniteDimensional ℚ F := hfinite
  letI : NumberField F := ⟨⟩
  have hfinal := ordinaryBorelMinimalCyclic_arithmetic_connection F a harith hmem r hr c hdata.1
  exact ⟨m,q,F,hmem,qF,hfinite,hmap,hq,hqF,hode,⟨inferInstance,r,hr,c,hfinal⟩,harith⟩

end StrictEUnit
end
