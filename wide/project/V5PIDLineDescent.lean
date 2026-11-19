import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import V5FiniteFaithfullyFlatDescent
import V5FaithfulUnitReflection
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit

/-- A torsion-free module over a PID whose faithfully flat scalar extension
is rank-one free is itself rank-one free. No global generator is supplied. -/
theorem v5_pid_line_equiv_of_faithfullyFlat
    {B R M : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B]
    [CommRing R] [Nontrivial R] [Algebra B R] [Module.FaithfullyFlat B R]
    [AddCommGroup M] [Module B M] [NoZeroSMulDivisors B M]
    (eR : R ⊗[B] M ≃ₗ[R] R) : Nonempty (B ≃ₗ[B] M) := by
  letI : Module.Finite R (R ⊗[B] M) := Module.Finite.equiv eR.symm
  letI : Module.Finite B M := v5_moduleFinite_of_faithfullyFlat_tensor (R := R)
  letI : Module.Free B M := Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank B M = 1 := by
    rw [← Module.finrank_baseChange (R := R)]
    exact (LinearEquiv.finrank_eq eR).trans (Module.finrank_self R)
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp hr
  refine ⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton B M v) ⟨?_, ?_⟩⟩
  · exact LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton B M hv)
  · exact hspan

/-- Tensoring an actual cyclic generator: every extended vector has that
same fixed right tensor factor. -/
theorem v5_tensor_eq_coefficient_generator
    {B R M : Type*} [CommRing B] [CommRing R] [Algebra B R]
    [AddCommGroup M] [Module B M] (e : B ≃ₗ[B] M) (x : R ⊗[B] M) :
    ∃ r : R, x = r ⊗ₜ[B] e 1 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r+s, (TensorProduct.add_tmul r s (e 1)).symm⟩
  | tmul r m =>
    have hm : m = e.symm m • e 1 := by rw [← e.map_smul]; simp
    refine ⟨e.symm m • r, ?_⟩
    calc
      r ⊗ₜ[B] m = r ⊗ₜ[B] (e.symm m • e 1) := congrArg (fun y => r ⊗ₜ[B] y) hm
      _ = (e.symm m • r) ⊗ₜ[B] e 1 := TensorProduct.smul_tmul _ _ _ |>.symm

/-- If the extended line contains an ambient unit, every actual free
generator has unit ambient value. This uses unit reflection, not a supplied
inverse or a supplied global weighted generator. -/
theorem v5_line_generator_isUnit_of_local_unit
    {B R M S T : Type*} [CommRing B] [CommRing R] [Algebra B R]
    [AddCommGroup M] [Module B M] [CommRing S] [Algebra B S]
    [CommRing T] [Algebra R T] [Algebra S T] [Module.FaithfullyFlat S T]
    (e : B ≃ₗ[B] M) (j : M →ₗ[B] S)
    (Ψ : R ⊗[B] M →ₗ[R] T)
    (hΨ : ∀ r m, Ψ (r ⊗ₜ[B] m) = algebraMap R T r * algebraMap S T (j m))
    (hunit : ∃ x : R ⊗[B] M, IsUnit (Ψ x)) : IsUnit (j (e 1)) := by
  obtain ⟨x, hx⟩ := hunit
  obtain ⟨r, hr⟩ := v5_tensor_eq_coefficient_generator e x
  rw [hr, hΨ] at hx
  exact v5_isUnit_of_faithfullyFlat (j (e 1)) (isUnit_of_mul_isUnit_right hx)

/-- Combined PID descent: the global free generator and its ambient unit
property are both conclusions, from a local rank-one trivialization and
one ambient unit in its extended image. -/
theorem v5_pid_line_unit_generator_of_faithfullyFlat
    {B R M S T : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B]
    [CommRing R] [Nontrivial R] [Algebra B R] [Module.FaithfullyFlat B R]
    [AddCommGroup M] [Module B M] [NoZeroSMulDivisors B M]
    [CommRing S] [Algebra B S]
    [CommRing T] [Algebra R T] [Algebra S T] [Module.FaithfullyFlat S T]
    (eR : R ⊗[B] M ≃ₗ[R] R) (j : M →ₗ[B] S)
    (Ψ : R ⊗[B] M →ₗ[R] T)
    (hΨ : ∀ r m, Ψ (r ⊗ₜ[B] m) = algebraMap R T r * algebraMap S T (j m))
    (hunit : ∃ x : R ⊗[B] M, IsUnit (Ψ x)) :
    ∃ e : B ≃ₗ[B] M, IsUnit (j (e 1)) := by
  obtain ⟨e⟩ := v5_pid_line_equiv_of_faithfullyFlat eR
  exact ⟨e, v5_line_generator_isUnit_of_local_unit e j Ψ hΨ hunit⟩

end StrictEUnit
#print axioms StrictEUnit.v5_pid_line_equiv_of_faithfullyFlat
#print axioms StrictEUnit.v5_tensor_eq_coefficient_generator
#print axioms StrictEUnit.v5_line_generator_isUnit_of_local_unit

#print axioms StrictEUnit.v5_pid_line_unit_generator_of_faithfullyFlat
