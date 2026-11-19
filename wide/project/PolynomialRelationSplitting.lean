import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Algebraic splitting of a genuine relation kernel over a PID.
No assertion about extra numerical relations at specialization is made. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

variable {R M N : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [NoZeroSMulDivisors R N]

/-- Actual functional-relation kernels are saturated when their target is torsion-free. -/
theorem relationKernel_saturated (F : M →ₗ[R] N) (a : R) (ha : a ≠ 0) (x : M) :
    a • x ∈ LinearMap.ker F ↔ x ∈ LinearMap.ker F := by
  simp only [LinearMap.mem_ker, map_smul, smul_eq_zero, ha, false_or]

/-- The quotient's free image gives an actual retraction onto the relation module.
This is only algebraic splitting, not arithmetic specialization surjectivity. -/
theorem relationKernel_exists_retraction (F : M →ₗ[R] N) :
    ∃ π : M →ₗ[R] LinearMap.ker F,
      π.comp (LinearMap.ker F).subtype = LinearMap.id := by
  letI : Module.Free R (LinearMap.range F) := Module.free_of_finite_type_torsion_free'
  have hsur : LinearMap.range F.rangeRestrict = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨s, hs⟩ := F.rangeRestrict.exists_rightInverse_of_surjective hsur
  have hsval (y : LinearMap.range F) : F (s y) = y.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hs y)
  let g : M →ₗ[R] M := LinearMap.id - s.comp F.rangeRestrict
  have hg (x : M) : g x ∈ LinearMap.ker F := by
    change F (x - s (F.rangeRestrict x)) = 0
    rw [map_sub, hsval]
    exact sub_self _
  let π : M →ₗ[R] LinearMap.ker F := g.codRestrict (LinearMap.ker F) hg
  refine ⟨π, ?_⟩
  ext x
  change x.val - s (F.rangeRestrict x.val) = x.val
  have hz : F.rangeRestrict x.val = 0 := Subtype.ext x.property
  rw [hz, map_zero, sub_zero]

/-- A finite relation kernel has a basis and a retraction, derived together. -/
theorem finiteRelationKernel_basis_retraction {ι : Type*} [Fintype ι]
    (F : (ι → R) →ₗ[R] N) :
    ∃ r : ℕ, ∃ b : Basis (Fin r) R (LinearMap.ker F),
      ∃ π : (ι → R) →ₗ[R] LinearMap.ker F,
        π.comp (LinearMap.ker F).subtype = LinearMap.id := by
  obtain ⟨r, b⟩ := Submodule.basisOfPid (Pi.basisFun R ι) (LinearMap.ker F)
  obtain ⟨π, hπ⟩ := relationKernel_exists_retraction F
  exact ⟨r, b, π, hπ⟩

/-- Coordinates of the retraction give a polynomial left inverse to the basis rows. -/
theorem relationKernel_basis_dual_certificate {ι : Type*} [Fintype ι]
    (F : (ι → R) →ₗ[R] N) (r : ℕ) (b : Basis (Fin r) R (LinearMap.ker F))
    (π : (ι → R) →ₗ[R] LinearMap.ker F)
    (hπ : π.comp (LinearMap.ker F).subtype = LinearMap.id) :
    ∃ c : Fin r → ι → R, ∀ i k,
      ∑ j, c i j * (b k).val j = if i = k then 1 else 0 := by
  classical
  let l (i : Fin r) : (ι → R) →ₗ[R] R := (b.coord i).comp π
  have hπx (x : LinearMap.ker F) : π x.val = x := LinearMap.congr_fun hπ x
  refine ⟨fun i j => l i ((Pi.basisFun R ι) j), ?_⟩
  intro i k
  have h := congrArg (l i) ((Pi.basisFun R ι).sum_repr (b k).val)
  simpa [map_sum, l, hπx, Basis.coord_apply, Finsupp.single_apply, eq_comm, mul_comm] using h

end StrictEUnit

namespace StrictEUnit
variable {R K ι α : Type*} [CommRing R] [CommRing K] [Fintype ι] [Fintype α] [DecidableEq α]

/-- A left inverse remains a left inverse at every specialization. This prevents
rank loss of a split polynomial relation basis, not new numerical relations. -/
theorem relationRows_specialization_independent (φ : R →+* K)
    (b : α → ι → R) (c : α → ι → R)
    (hc : ∀ i k, ∑ j, c i j * b k j = if i = k then 1 else 0) :
    LinearIndependent K (fun k j => φ (b k j)) := by
  classical
  let T : (ι → K) →ₗ[K] (α → K) :=
    LinearMap.pi (fun i => ∑ j, φ (c i j) • LinearMap.proj j)
  have hT (k : α) : T (fun j => φ (b k j)) = (Pi.basisFun K α) k := by
    funext i
    have h := congrArg φ (hc i k)
    simpa [T, Pi.basisFun_apply, Pi.single_apply, eq_comm] using h
  apply LinearIndependent.of_comp T
  have heq : T ∘ (fun k j => φ (b k j)) = Pi.basisFun K α := funext hT
  rw [heq]
  exact (Pi.basisFun K α).linearIndependent

end StrictEUnit


namespace StrictEUnit
/-- A polynomial relation kernel into a torsion-free target has one basis whose
rows stay independent at every point. This is not a claim about the whole
numerical relation space at any point. -/
theorem polynomialRelationKernel_specialization_basis
    {K N ι : Type*} [Field K] [AddCommGroup N] [Module (Polynomial K) N]
    [NoZeroSMulDivisors (Polynomial K) N] [Fintype ι]
    (F : (ι → Polynomial K) →ₗ[Polynomial K] N) :
    ∃ r : ℕ, ∃ b : Basis (Fin r) (Polynomial K) (LinearMap.ker F),
      ∀ a : K, LinearIndependent K (fun i j => ((b i).val j).eval a) := by
  obtain ⟨r, b, π, hπ⟩ := finiteRelationKernel_basis_retraction F
  obtain ⟨c, hc⟩ := relationKernel_basis_dual_certificate F r b π hπ
  refine ⟨r, b, fun a => ?_⟩
  exact relationRows_specialization_independent (Polynomial.evalRingHom a)
    (fun i => (b i).val) c hc
end StrictEUnit

