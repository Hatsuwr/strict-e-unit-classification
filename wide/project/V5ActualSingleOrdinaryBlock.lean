import V5BroadNormBlockEndpoint
import OrdinaryBorelMinimalCyclic
import OrdinaryRegularDenominatorClearing

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 75000
open scoped BigOperators
namespace StrictEUnit
local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

/-- A single ordinary independent derivative block is enough for the exact
quotient contradiction. This version uses the supplied minimal cyclic row. -/
theorem v5_actual_minimal_ordinary_block_quotient_impossible
    (F : subfieldEntireFunctionAlgebra k)
    (r : ℕ) (hr : 0 < r) (b : Fin r → RatFunc k)
    (hc : OrdinaryBorelMinimalCyclicData (v5ActualEntireLaurentAlgHom k F) r b)
    (hreg : ∀ i, ∃ S : PowerSeries k,
      HahnSeries.ofPowerSeries ℤ k S = ordinaryPointRationalMap 1 (b i))
    (m : ℕ) (p : Fin (m+1) → Polynomial k)
    (hord : (p (Fin.last m)).eval 1 ≠ 0)
    (hsource : (∑ i, algebraMap (Polynomial k) (LaurentSeries k) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val]
        (v5NormLaurentQuotient F)) = 0) : False := by
  classical
  let H := v5ActualEntireLaurentAlgHom k
  let g := v5ActualEntireDerivativeCoordinates k F (fun i : Fin r => i.val)
  let i₀ : Fin r := ⟨0,hr⟩
  let B : Matrix (Fin r) (Fin r) (RatFunc k) := minimalDerivativeCompanion r b
  obtain ⟨T,hT,U,hU⟩ := exists_ordinary_minimal_companion_clearing 1 r b hreg
  have hkeep : g i₀ = F := v5_actualEntireDerivativeCoordinates_zero k F _ i₀ rfl
  have hform (i : Fin r) : H (g i) =
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[i.val] (H F) :=
    v5_actualEntireDerivativeCoordinates_laurent k F _ i
  have hli : LinearIndependent (RatFunc k) (fun i => H (g i)) := by
    simp_rw [hform]
    exact hc.1
  have hsys (i : Fin r) : laurentOrdinaryDerivation (H (g i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B i j) * H (g j) := by
    simp_rw [hform]
    simpa only [Algebra.smul_def,B] using hc.2.2.2.2 i
  refine v5_actual_ordinary_blocks_quotient_contradiction k (S := Unit) (n := fun _ => r)
    (fun _ => F) (fun _ => g) (fun _ => i₀) (fun _ => hkeep) (fun _ => B)
    (fun _ => T) (fun _ => U) (fun _ => hT) (fun _ => hU) (fun _ => hli)
    (fun _ => hsys) m p hord ?_
  have he : v5NormLaurentQuotient F =
      algebraMap (RatFunc k) (LaurentSeries k) (ordinaryPointInverseLinear (1 : k)) *
        ∏ _ : Unit, H F := by
    unfold v5NormLaurentQuotient ordinaryPointInverseLinear
    rw [map_inv₀, ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k),
      Polynomial.C_1]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]
    rfl
  rwa [he] at hsource

#print axioms v5_actual_minimal_ordinary_block_quotient_impossible
end StrictEUnit
