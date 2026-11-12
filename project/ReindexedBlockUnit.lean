import ActualFourierClassAssembly
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {C : Type*} {I : C → Type*} {J R : Type*}
  [Fintype C] [DecidableEq C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
  [Fintype J] [DecidableEq J] [CommRing R]

def reindexedBlockUnit (Z : ∀ c, (Matrix (I c) (I c) R)ˣ)
    (e : (Σ c, I c) ≃ J) : (Matrix J J R)ˣ :=
  Units.map (Matrix.reindexAlgEquiv R R e).toMonoidHom (finiteBlockUnit Z)

theorem reindexedBlockUnit_row (Z : ∀ c, (Matrix (I c) (I c) R)ˣ)
    (e : (Σ c, I c) ≃ J) (f : ∀ c, I c → R) (j : J) :
    (∑ i : J, f (e.symm i).1 (e.symm i).2 * (reindexedBlockUnit Z e).val i j) =
      ∑ i : I (e.symm j).1, f (e.symm j).1 i * (Z (e.symm j).1).val i (e.symm j).2 := by
  change (∑ i : J, f (e.symm i).1 (e.symm i).2 *
    (finiteBlockUnit Z).val (e.symm i) (e.symm j)) = _
  rw [e.symm.sum_comp (fun i => f i.1 i.2 * (finiteBlockUnit Z).val i (e.symm j))]
  exact finiteBlockUnit_row Z f (e.symm j).1 (e.symm j).2

def analyticLaurentLogImage (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :
    Polynomial (LaurentSeries AlgebraicComplex) :=
  Polynomial.C (show LaurentSeries AlgebraicComplex from
    stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield F)

local instance analyticLogRing : CommRing (Polynomial (LaurentSeries AlgebraicComplex)) := inferInstance

theorem reindexedBlockUnit_analytic_row
    (Z : ∀ c, (Matrix (I c) (I c) (Polynomial (LaurentSeries AlgebraicComplex)))ˣ)
    (e : (Σ c, I c) ≃ J)
    (F : ∀ c, I c → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) (j : J) :
    (∑ i : J, analyticLaurentLogImage (F (e.symm i).1 (e.symm i).2) *
      (reindexedBlockUnit (C := C) (I := I) (J := J) (R := Polynomial (LaurentSeries AlgebraicComplex)) Z e).val i j) =
    ∑ i : I (e.symm j).1, analyticLaurentLogImage (F (e.symm j).1 i) *
      (Z (e.symm j).1).val i (e.symm j).2 := by
  exact reindexedBlockUnit_row (C := C) (I := I) (J := J) (R := Polynomial (LaurentSeries AlgebraicComplex)) Z e (fun c i => analyticLaurentLogImage (F c i)) j

end StrictEUnit
end
