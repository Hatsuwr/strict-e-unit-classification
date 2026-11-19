import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

/-- Units descend through a faithfully flat commutative algebra map. -/
theorem v5_isUnit_of_faithfullyFlat {B S : Type*}
    [CommRing B] [CommRing S] [Algebra B S] [Module.FaithfullyFlat B S]
    (x : B) (h : IsUnit (algebraMap B S x)) : IsUnit x := by
  let f : B →ₗ[B] B := (LinearMap.lsmul B B).flip x
  let e := Algebra.TensorProduct.rid B S S
  have he (y : S ⊗[B] B) : e (f.lTensor S y) = algebraMap B S x * e y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, mul_add]
    | tmul s b =>
      change _ = _
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.rid_tmul]
      rw [Algebra.smul_def, Algebra.smul_def]
      change algebraMap B S (b * x) * s = _
      rw [map_mul]
      ac_rfl
  have surj : Function.Surjective (f.lTensor S) := by
    obtain ⟨u,hu⟩ := h
    intro y
    refine ⟨e.symm ((↑u⁻¹ : S) * e y), e.injective ?_⟩
    rw [he, e.apply_symm_apply, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨b, hb⟩ := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective B S f).mp surj 1
  exact isUnit_iff_dvd_one.mpr ⟨b, by simpa [f, mul_comm] using hb.symm⟩

end StrictEUnit
#print axioms StrictEUnit.v5_isUnit_of_faithfullyFlat
