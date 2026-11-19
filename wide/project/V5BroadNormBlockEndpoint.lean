import V5ActualBlockQuotientContradiction
import V5BroadNormQuotientAnnihilator

noncomputable section
open scoped BigOperators
namespace StrictEUnit
local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

/-- A rational broad norm vanishing at one cannot be assembled from full
ordinary independent blocks with every original factor still a coordinate. -/
theorem v5_broad_norm_ordinary_blocks_impossible {S : Type*} [Fintype S] {n : S → ℕ}
    (f : S → subfieldEntireFunctionAlgebra k)
    (F : subfieldEntireFunctionAlgebra k) (hF : F = ∏ s, f s)
    (c : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun j => (c j : ℂ)*z^j/(j.factorial : ℂ)) (F.val.val z))
    (hODE : HasAlgebraicPolynomialODE F.val.val)
    (ha : V5BroadAlgebraicArithmetic c)
    (hrat : ∀ j, ∃ q : ℚ, c j = algebraMap ℚ AlgebraicComplex q)
    (hzero : F.val.val 1 = 0) (hne : F.val.val ≠ 0)
    (g : ∀ s, Fin (n s) → subfieldEntireFunctionAlgebra k)
    (a : ∀ s, Fin (n s)) (hkeep : ∀ s, g s (a s) = f s)
    (B : ∀ s, Matrix (Fin (n s)) (Fin (n s)) (RatFunc k))
    (T : S → Polynomial k) (U : ∀ s, Matrix (Fin (n s)) (Fin (n s)) (Polynomial k))
    (hT : ∀ s, (T s).eval 1 ≠ 0)
    (hU : ∀ s i j, algebraMap (Polynomial k) (RatFunc k) (U s i j) =
      algebraMap (Polynomial k) (RatFunc k) (T s) * B s i j)
    (hlin : ∀ s, LinearIndependent (RatFunc k)
      (fun j => v5ActualEntireLaurentAlgHom k (g s j)))
    (hsys : ∀ s i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (g s i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B s i j) *
        v5ActualEntireLaurentAlgHom k (g s j)) : False := by
  obtain ⟨m,p,_,hord,hop⟩ := v5_broad_norm_quotient_ordinary_annihilator F c hs hODE ha hrat hzero hne
  refine v5_actual_ordinary_blocks_quotient_contradiction k f g a hkeep B T U hT hU hlin hsys
    m p hord ?_
  have hq : v5NormLaurentQuotient F =
      algebraMap (RatFunc k) (LaurentSeries k) (ordinaryPointInverseLinear (1 : k)) *
        ∏ s, v5ActualEntireLaurentAlgHom k (f s) := by
    unfold v5NormLaurentQuotient ordinaryPointInverseLinear
    rw [map_inv₀, ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k),
      Polynomial.C_1, hF, map_prod]; rfl
  rwa [hq] at hop

#print axioms v5_broad_norm_ordinary_blocks_impossible
end StrictEUnit
