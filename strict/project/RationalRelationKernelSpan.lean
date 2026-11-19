import FormalPolynomialRelationBasis
import Stage14ActualAnalyticODETransfer
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Common denominators connect the actual polynomial and rational relation
kernels. No denominator is evaluated or cancelled at a specialization point. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem relationKernel_fraction_span_basis
    {A B M ι κ : Type*}
    [CommRing A] [IsDomain A] [Field B]
    [Algebra A B] [IsFractionRing A B]
    [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Fintype ι]
    (f : ι → M)
    (b : Basis κ A (LinearMap.ker (Fintype.linearCombination A f))) :
    LinearMap.ker (Fintype.linearCombination B f) =
      Submodule.span B (Set.range (fun k j => algebraMap A B ((b k).val j))) := by
  classical
  let E : (ι → A) →ₗ[A] (ι → B) := (Algebra.linearMap A B).compLeft ι
  let S : Submodule B (ι → B) :=
    Submodule.span B (Set.range (fun k j => algebraMap A B ((b k).val j)))
  have hcompat (p : ι → A) : Fintype.linearCombination B f (E p) =
      Fintype.linearCombination A f p := by
    change (∑ j, algebraMap A B (p j) • f j) = ∑ j, p j • f j
    simp only [IsScalarTower.algebraMap_smul B]
  have hS (p : LinearMap.ker (Fintype.linearCombination A f)) : E p.val ∈ S := by
    let E' : LinearMap.ker (Fintype.linearCombination A f) →ₗ[A] (ι → B) :=
      E.comp (LinearMap.ker (Fintype.linearCombination A f)).subtype
    have hle : Submodule.span A (Set.range b) ≤ (S.restrictScalars A).comap E' := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change E (b i).val ∈ S
      exact Submodule.subset_span ⟨i, rfl⟩
    exact hle (b.mem_span p)
  change LinearMap.ker (Fintype.linearCombination B f) = S
  apply le_antisymm
  · intro q hq
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) q
    choose p hp using hd
    have hdne : algebraMap A B (d : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property
    have hrow : E p = algebraMap A B (d : A) • q := by
      funext j
      change algebraMap A B (p j) = algebraMap A B (d : A) * q j
      simpa only [Algebra.smul_def] using hp j
    have hpoly : p ∈ LinearMap.ker (Fintype.linearCombination A f) := by
      change Fintype.linearCombination A f p = 0
      rw [← hcompat p, hrow, map_smul]
      rw [show Fintype.linearCombination B f q = 0 from hq, smul_zero]
    have hdmem : algebraMap A B (d : A) • q ∈ S := by
      rw [← hrow]
      exact hS ⟨p, hpoly⟩
    exact (S.smul_mem_iff hdne).mp hdmem
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change Fintype.linearCombination B f (E (b i).val) = 0
    rw [hcompat]
    exact (b i).property

theorem formalRationalRelationKernel_span_basis
    {K ι : Type*} [Field K] [Fintype ι]
    (f : ι → LaurentSeries K) (r : ℕ)
    (b : Basis (Fin r) (Polynomial K) (LinearMap.ker (formalPolynomialRelationMap f))) :
    LinearMap.ker (Fintype.linearCombination (RatFunc K) f) =
      Submodule.span (RatFunc K) (Set.range (fun i j =>
        algebraMap (Polynomial K) (RatFunc K) ((b i).val j))) := by
  exact relationKernel_fraction_span_basis f b

theorem formalRationalRelationKernel_basis_independent
    {K ι : Type*} [Field K] [Fintype ι]
    (f : ι → LaurentSeries K) (r : ℕ)
    (b : Basis (Fin r) (Polynomial K) (LinearMap.ker (formalPolynomialRelationMap f))) :
    LinearIndependent (RatFunc K) (fun i j =>
      algebraMap (Polynomial K) (RatFunc K) ((b i).val j)) := by
  letI : NoZeroSMulDivisors (Polynomial K) (LaurentSeries K) :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr
      (Polynomial.algebraMap_hahnSeries_injective ℤ)
  obtain ⟨π, hπ⟩ := relationKernel_exists_retraction (formalPolynomialRelationMap f)
  obtain ⟨c, hc⟩ := relationKernel_basis_dual_certificate
    (formalPolynomialRelationMap f) r b π hπ
  exact relationRows_specialization_independent
    (algebraMap (Polynomial K) (RatFunc K)) (fun i => (b i).val) c hc

theorem formalRationalRelationKernel_finrank
    {K ι : Type*} [Field K] [Fintype ι]
    (f : ι → LaurentSeries K) (r : ℕ)
    (b : Basis (Fin r) (Polynomial K) (LinearMap.ker (formalPolynomialRelationMap f))) :
    Module.finrank (RatFunc K) (LinearMap.ker (Fintype.linearCombination (RatFunc K) f)) = r := by
  rw [formalRationalRelationKernel_span_basis f r b]
  simpa only [Fintype.card_fin] using finrank_span_eq_card
    (formalRationalRelationKernel_basis_independent f r b)

theorem formalRelationQuotient_finrank_add
    {K ι : Type*} [Field K] [Fintype ι]
    (f : ι → LaurentSeries K) (r : ℕ)
    (b : Basis (Fin r) (Polynomial K) (LinearMap.ker (formalPolynomialRelationMap f))) :
    Module.finrank (RatFunc K)
      ((ι → RatFunc K) ⧸ LinearMap.ker (Fintype.linearCombination (RatFunc K) f)) + r =
        Fintype.card ι := by
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (Fintype.linearCombination (RatFunc K) f))
  simpa only [formalRationalRelationKernel_finrank f r b, Module.finrank_fintype_fun_eq_card] using h

/-- The very same polynomial tuple gives a relation in the actual Laurent
image exactly when it is a global relation of the original entire family. -/
theorem actualFamily_polynomial_relation_iff
    {ι : Type*} [Fintype ι] (k : Subfield ℂ)
    (F : ι → subfieldEntireFunctionAlgebra k) (p : ι → Polynomial k) :
    p ∈ LinearMap.ker (formalPolynomialRelationMap
      (fun i => stage14_subfieldEntireLaurentAlgHom k (F i))) ↔
      ∀ z : ℂ, ∑ i, (p i).eval₂ k.subtype z * (F i).val.val z = 0 := by
  letI : AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
    @NonUnitalNonAssocSemiring.toAddCommMonoid _
      (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
        (@Semiring.toNonAssocSemiring _
          (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))
  let R : subfieldEntireFunctionAlgebra k :=
    ∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) * F i
  have hmap : stage14_subfieldEntireLaurentAlgHom k R =
      formalPolynomialRelationMap (fun i => stage14_subfieldEntireLaurentAlgHom k (F i)) p := by
    dsimp only [R, formalPolynomialRelationMap, Fintype.linearCombination_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, stage14_subfieldEntireLaurentAlgHom_polynomial, Algebra.smul_def]
  have heval (z : ℂ) : stage14_subfieldEntireEvaluation k z R =
      ∑ i, (p i).eval₂ k.subtype z * (F i).val.val z := by
    dsimp only [R]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, stage14_subfieldEntireEvaluation_polynomial]
    rfl
  have hzero : R = 0 ↔ ∀ z : ℂ, ∑ i, (p i).eval₂ k.subtype z * (F i).val.val z = 0 := by
    constructor
    · intro h z
      rw [← heval, h, map_zero]
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change stage14_subfieldEntireEvaluation k z R = 0
      rw [heval, h]
  rw [← hzero]
  change formalPolynomialRelationMap _ p = 0 ↔ R = 0
  rw [← hmap]
  exact map_eq_zero_iff _ (stage14_subfieldEntireLaurentAlgHom_injective k)
end StrictEUnit
