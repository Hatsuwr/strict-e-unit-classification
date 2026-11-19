import V5BroadDerivativePrefix
import V5BroadBorelEntireBridge

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Broad arithmetic of the original coefficients and a nonzero factorial
series equation over their number field suffice for an entire annihilator
whose leading polynomial is nonzero at every nonzero complex point. -/
theorem v5_broad_entire_annihilator_ordinary_off_zero
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (a : ℕ → K) (ha : V5BroadArithmetic a) (hne : ∃ n, a n ≠ 0)
    (f : entireFunctionAlgebra)
    (hcoeff : ∀ n, φ (a n) = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (m : ℕ) (p : Fin (m+1) → Polynomial K) (hp : ∃ i, p i ≠ 0)
    (hode : (∑ i, (p i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : K)))) = 0) :
    ∃ (n : ℕ) (P : ℕ → Polynomial ℂ), 0 < n ∧
      (∀ z, v5RowResidual f.val n P z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (P n).eval z ≠ 0 :=
  v5_broad_entire_annihilator_of_prefixes φ a hne f hcoeff m p hp hode
    (v5_broad_ordinaryDerivativePrefix a ha)

#print axioms v5_broad_entire_annihilator_ordinary_off_zero
end StrictEUnit
end
