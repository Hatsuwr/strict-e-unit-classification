import AbsoluteRelationIdeal
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Degree-one relations supported on an independent subfamily remain trivial
after coefficient extension. No geometric-integrality or primality is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct BigOperators
namespace StrictEUnit

theorem mvEval_linearForm_smul
    {L T σ τ : Type*} [CommRing L] [CommRing T] [Algebra L T] [Fintype τ]
    (z : σ → T) (j : τ → σ) (c : τ → L) :
    MvPolynomial.eval₂Hom (algebraMap L T) z
      (∑ a, MvPolynomial.C (c a) * MvPolynomial.X (j a)) =
      ∑ a, c a • z (j a) := by
  simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Algebra.smul_def]

theorem relationIdeal_map_linearForm_coefficients_zero
    {F E L σ τ : Type*} [Field F] [CommRing E] [Algebra F E]
    [CommRing L] [Algebra F L] [Fintype τ]
    (y : σ → E) (j : τ → σ)
    (hy : LinearIndependent F (fun a => y (j a)))
    (c : τ → L)
    (hc : (∑ a, MvPolynomial.C (c a) * MvPolynomial.X (j a)) ∈
      (RingHom.ker (MvPolynomial.eval₂Hom (algebraMap F E) y)).map
        (MvPolynomial.map (algebraMap F L))) :
    ∀ a, c a = 0 := by
  classical
  let f : MvPolynomial σ F →ₐ[F] E := MvPolynomial.aeval y
  let I : Ideal (MvPolynomial σ F) := RingHom.ker f
  let C := MvPolynomial σ F ⧸ I
  let q : MvPolynomial σ F →ₐ[F] C := Ideal.Quotient.mkₐ F I
  let x : σ → C := fun i => q (MvPolynomial.X i)
  have hx : LinearIndependent F (fun a => x (j a)) := by
    apply LinearIndependent.of_comp (Ideal.kerLiftAlg f).toLinearMap
    change LinearIndependent F (fun a => Ideal.kerLiftAlg f
      (Ideal.Quotient.mk (RingHom.ker f) (MvPolynomial.X (j a))))
    simpa only [Ideal.kerLiftAlg_mk, f, MvPolynomial.aeval_X] using hy
  let T := L ⊗[F] C
  letI : CommRing T := Algebra.TensorProduct.instCommRing
  let ι : C →ₐ[F] T := Algebra.TensorProduct.includeRight
  let φ : MvPolynomial σ L →+* T :=
    MvPolynomial.eval₂Hom (algebraMap L T) (fun i => ι (x i))
  have hcomp : φ.comp (MvPolynomial.map (algebraMap F L)) =
      ι.toRingHom.comp q.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, φ, MvPolynomial.eval₂Hom_C]
      change algebraMap L T (algebraMap F L a) = ι (q (MvPolynomial.C a))
      rw [show q (MvPolynomial.C a) = algebraMap F C a from q.commutes a,
        ι.commutes]
      exact (IsScalarTower.algebraMap_apply F L T a).symm
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X,
        φ, MvPolynomial.eval₂Hom_X']
      rfl
  have hle : I.map (MvPolynomial.map (algebraMap F L)) ≤ RingHom.ker φ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change φ (MvPolynomial.map (algebraMap F L) p) = 0
    change φ.comp (MvPolynomial.map (algebraMap F L)) p = 0
    rw [hcomp]
    change ι (q p) = 0
    have hq : q p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [hq, map_zero]
  have hzero : φ (∑ a, MvPolynomial.C (c a) * MvPolynomial.X (j a)) = 0 := hle hc
  have hbase : LinearIndependent L (fun a => (1 : L) ⊗ₜ[F] x (j a)) :=
    Module.Flat.linearIndependent_one_tmul hx
  apply Fintype.linearIndependent_iff.mp hbase c
  change (∑ a, c a • ((1 : L) ⊗ₜ[F] x (j a))) = 0
  have heval := mvEval_linearForm_smul (fun i => ι (x i)) j c
  change φ (∑ a, MvPolynomial.C (c a) * MvPolynomial.X (j a)) =
    (∑ a, c a • ((1 : L) ⊗ₜ[F] x (j a))) at heval
  rw [← heval]
  exact hzero

end StrictEUnit
