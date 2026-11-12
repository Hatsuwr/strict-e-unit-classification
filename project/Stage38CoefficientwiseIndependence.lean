import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Independence under literal coefficientwise extension of fields

An injective semilinear map need not preserve independence over the larger
field. Here the stronger coefficientwise property supplies the missing fact:
apply every K-linear functional L → K to a finite L-relation, then use dual
separation. No finiteness of the family or of the field extension is needed.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {K L ι S : Type*} [Field K] [Field L] [Algebra K L]

/-- Literal coefficientwise scalar extension preserves independence. -/
theorem stage38_coefficientwise_linearIndependent
    (v : ι → S → K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i s => algebraMap K L (v i s)) := by
  classical
  apply linearIndependent_iff'.2
  intro t c hc i hi
  apply (Module.forall_dual_apply_eq_zero_iff K (c i)).mp
  intro φ
  apply linearIndependent_iff'.1 hv t (fun j => φ (c j)) ?_ i hi
  funext s
  have hs := congrArg (fun f : S → L => φ (f s)) hc
  have hs' : ∑ j ∈ t, v j s * φ (c j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    map_sum, map_zero, mul_comm (c _) (algebraMap K L _),
      ← Algebra.smul_def, map_smul] using hs
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using hs'

/-- Coordinate-extraction version. Both coefficient maps are linear and the
source map is injective; the target family has the literal extended coefficients.
The target coefficient map need not be injective for this direction. -/
theorem stage38_linearIndependent_of_extended_coefficients
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    (a : V →ₗ[K] (S → K)) (ha : Function.Injective a)
    (b : W →ₗ[L] (S → L)) (v : ι → V) (w : ι → W)
    (hcoeff : ∀ i s, b (w i) s = algebraMap K L (a (v i) s))
    (hv : LinearIndependent K v) : LinearIndependent L w := by
  have hv' : LinearIndependent K (fun i => a (v i)) := hv.map' a (LinearMap.ker_eq_bot.mpr ha)
  have hw' := stage38_coefficientwise_linearIndependent (L := L) _ hv'
  have heq : (fun i => b (w i)) = (fun i s => algebraMap K L (a (v i) s)) := by
    funext i s
    exact hcoeff i s
  rw [← heq] at hw'
  exact hw'.of_comp b

end StrictEUnit
