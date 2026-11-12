import AugmentedCompanionScalarEquivalence
import SameCompanionEulerGaugeConnection
import ReflectedFourierOrdinaryBridge
import SameCompanionEulerScalarAction

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The mapped original companion is precisely the companion of its mapped
coefficients; the order and source coefficients are unchanged. -/
theorem originalSource_companion_laurent_map (n : ℕ) (c : Fin (n+1) → RatFunc K) :
    Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K))=
      minimalDerivativeCompanion (n+1) (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j)) := by
  funext i j
  simp only [Matrix.map_apply,minimalDerivativeCompanion]
  split_ifs <;> simp

/-- Canonical Laurent derivation and the actual power-series derivative
commute through the fixed inclusion, at every order. -/
theorem originalSource_laurent_iterate_powerSeries (G : PowerSeries K) (m : ℕ) :
    (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[m]
      (HahnSeries.ofPowerSeries ℤ K G)=
    HahnSeries.ofPowerSeries ℤ K ((PowerSeries.derivative K)^[m] G) := by
  have hD : (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)=
      laurentOrdinaryDerivation := funext stage14_laurentAlgebraDerivation_apply
  rw [hD]
  exact laurentOrdinaryDerivation_iterate_ofPowerSeries G m

/-- Exact residual identity with the ORIGINAL unreflected polynomial tuple.
It holds for every ordinary formal G, without a homogeneous-solution premise. -/
theorem originalSource_companion_residual_powerSeries
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (G : PowerSeries K) :
    sourceCompanionResidual n (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j))
      (polynomialLaurentImage T) (HahnSeries.ofPowerSeries ℤ K G)=
    HahnSeries.ofPowerSeries ℤ K
      (reciprocalOrdinarySourceAction (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U) G) := by
  have hidx : (⟨n+1-1,by omega⟩ : Fin (n+1))=Fin.last n := by apply Fin.ext;simp
  have hU : ∀ j,polynomialLaurentImage (U (Fin.last n) j)=polynomialLaurentImage T*
      algebraMap (RatFunc K) (LaurentSeries K) (c j) := by
    intro j
    simpa only [minimalDerivativeCompanion,Fin.val_last,lt_self_iff_false,ite_false] using
      same_companion_laurent_clearing n c T U hclear (Fin.last n) j
  have hQ : reciprocalOrdinarySourceAction (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U) G=
      (T : PowerSeries K)*(PowerSeries.derivative K)^[n+1] G-
      ∑ j,(U (Fin.last n) j : PowerSeries K)*(PowerSeries.derivative K)^[j.val] G :=
    sameCompanionPowerSeriesScalarAction_eq_last_sub n T U G
  rw [hQ]
  unfold sourceCompanionResidual sourceOrdinaryDerivativeJet
  simp only [map_sub,map_mul,map_sum,originalSource_laurent_iterate_powerSeries]
  change polynomialLaurentImage T*((HahnSeries.ofPowerSeries ℤ K) ((PowerSeries.derivative K)^[n+1] G)-
    ∑ j,algebraMap (RatFunc K) (LaurentSeries K) (c j)*
      (HahnSeries.ofPowerSeries ℤ K) ((PowerSeries.derivative K)^[j.val] G))=
    polynomialLaurentImage T*(HahnSeries.ofPowerSeries ℤ K) ((PowerSeries.derivative K)^[n+1] G)-
    ∑ j,polynomialLaurentImage (U (Fin.last n) j)*
      (HahnSeries.ofPowerSeries ℤ K) ((PowerSeries.derivative K)^[j.val] G)
  rw [mul_sub,Finset.mul_sum]
  simp only [hU,mul_assoc]

/-- Actual augmented source equation and the literal finite forcing matrix
are equivalent on the canonical lift of every ordinary source G. -/
theorem originalSource_augmented_matrix_iff
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (G : PowerSeries K) (d : ℕ) :
    let cL := fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j)
    let tL := polynomialLaurentImage T
    let v := augmentedSourceJet n cL tL (HahnSeries.ofPowerSeries ℤ K G) d
    (∀ i,stage14_laurentAlgebraDerivation (v i)=
      ∑ j,polynomialForcingConnection
        (Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K)))
        (fun i =>if i.val+1=n+1 then tL⁻¹ else 0) d i j*v j) ↔
      (PowerSeries.derivative K)^[d+1]
        (reciprocalOrdinarySourceAction (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U) G)=0 := by
  dsimp only
  rw [originalSource_companion_laurent_map,
    augmentedCompanion_scalar_lift_iff n _ _ _ (polynomialLaurentImage_ne_zero T hT),
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
