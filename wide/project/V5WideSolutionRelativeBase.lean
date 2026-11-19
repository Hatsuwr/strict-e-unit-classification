import V5WideSolutionBase

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

abbrev V5LaurentBase := LaurentPolynomial AlgebraicComplex

instance v5WideSolutionLaurentAlgebra {ι : Type} (f : ι → entireFunctionAlgebra) :
    Algebra V5LaurentBase (v5WideSolutionAlgebra f) :=
  (v5WideSolutionBase f).toRingHom.toAlgebra

instance v5WideSolutionLaurentTower {ι : Type} (f : ι → entireFunctionAlgebra) :
    IsScalarTower AlgebraicComplex V5LaurentBase (v5WideSolutionAlgebra f) :=
  IsScalarTower.of_algebraMap_eq' (v5WideSolutionBase f).comp_algebraMap.symm

@[simp] theorem v5WideSolutionLaurent_algebraMap {ι : Type} (f : ι → entireFunctionAlgebra)
    (b : V5LaurentBase) :
    algebraMap V5LaurentBase (v5WideSolutionAlgebra f) b = v5WideSolutionBase f b := rfl

theorem v5WideSolutionLaurent_generates {ι : Type} (f : ι → entireFunctionAlgebra) :
    Algebra.adjoin V5LaurentBase (Set.range (v5WideSolutionEntry f)) = ⊤ := by
  apply top_unique
  intro x hxTop
  clear hxTop
  let K := Algebra.adjoin V5LaurentBase (Set.range (v5WideSolutionEntry f))
  change x ∈ K
  rcases x with ⟨x, hx⟩
  change x ∈ Algebra.adjoin AlgebraicComplex _ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨b, rfl⟩
    · exact Algebra.subset_adjoin (Set.mem_range_self i)
    · change v5WideSolutionParameter f b ∈ K
      cases b
      · have hm := K.algebraMap_mem (LaurentPolynomial.T (-1))
        change v5WideSolutionBase f (LaurentPolynomial.T (-1)) ∈ K at hm
        change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) (LaurentPolynomial.T (-1)) ∈ K at hm
        rwa [LaurentPolynomial.eval₂_T, zpow_neg_one] at hm
      · have hm := K.algebraMap_mem (LaurentPolynomial.T 1)
        change v5WideSolutionBase f (LaurentPolynomial.T 1) ∈ K at hm
        change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) (LaurentPolynomial.T 1) ∈ K at hm
        rwa [LaurentPolynomial.eval₂_T, zpow_one] at hm
  | algebraMap a => exact (K.restrictScalars AlgebraicComplex).algebraMap_mem a
  | add x y hx hy ihx ihy => exact K.add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact K.mul_mem ihx ihy

end StrictEUnit
#print axioms StrictEUnit.v5WideSolutionLaurent_generates
