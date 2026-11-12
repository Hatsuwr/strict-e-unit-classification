import AugmentedSourceEulerMatrix
import MonomialEulerSolutionTransport
import OriginalSourceAugmentedIdentification

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Literal weighted canonical source lift, including the actual residual
forcing derivatives. No arbitrary forcing polynomial replaces the residual. -/
def augmentedSourceEulerJet (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (f : LaurentSeries K) (d : ℕ) :
    Fin (((n+1)+1)+d) →LaurentSeries K := fun i =>
  laurentIntegerMonomial (augmentedSourceEulerWeights n T d i : ℤ)*
    augmentedSourceJet n (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j))
      (polynomialLaurentImage T) f d i

/-- Exact realization of D^(d+1)Qf=0 for the ORIGINAL unreflected source Q
as the constructed regular Euler matrix on its canonical weighted jet. -/
theorem augmentedSourceEulerJet_solution_iff
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : LaurentSeries K) (d : ℕ) :
    (∀ i,laurentEuler (augmentedSourceEulerJet n c T f d i)=
      ∑ j,HahnSeries.ofPowerSeries ℤ K (augmentedSourceEulerMatrix n T U d i j)*
        augmentedSourceEulerJet n c T f d j) ↔
    (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1]
      (sourceCompanionResidual n (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j))
        (polynomialLaurentImage T) f)=0 := by
  have he := monomialEulerPresentation_solution_iff _ _ _
    (augmentedSourceEulerMatrix_realization n c T U hT hclear hV d)
    (augmentedSourceJet n (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j))
      (polynomialLaurentImage T) f d)
  change _ ↔_ at he
  unfold augmentedSourceEulerJet
  rw [← he,originalSource_companion_laurent_map]
  exact augmentedCompanion_scalar_lift_iff n _ _ f (polynomialLaurentImage_ne_zero T hT) d

/-- Ordinary source power series recover the actual augmented original
polynomial operator, not a reflected or substitute scalar tuple. -/
theorem augmentedSourceEulerJet_powerSeries_iff
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1))
    (G : PowerSeries K) (d : ℕ) :
    (∀ i,laurentEuler (augmentedSourceEulerJet n c T (HahnSeries.ofPowerSeries ℤ K G) d i)=
      ∑ j,HahnSeries.ofPowerSeries ℤ K (augmentedSourceEulerMatrix n T U d i j)*
        augmentedSourceEulerJet n c T (HahnSeries.ofPowerSeries ℤ K G) d j) ↔
    (PowerSeries.derivative K)^[d+1]
      (reciprocalOrdinarySourceAction (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U) G)=0 := by
  rw [augmentedSourceEulerJet_solution_iff n c T U hT hclear hV,
    originalSource_companion_residual_powerSeries n c T U hclear,
    originalSource_laurent_iterate_powerSeries]
  constructor
  · intro h
    apply HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (R:=K)
    simpa only [map_zero] using h
  · intro h
    rw [h,map_zero]

end StrictEUnit
end
