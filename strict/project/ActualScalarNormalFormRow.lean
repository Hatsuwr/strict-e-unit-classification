import Stage33ScalarNormalFormData
import NaturalClassRamifiedExponent
noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem scalarNormalFormRow_as_logAmbient (k : Subfield ℂ)
    {I : Type*} [Fintype I] [DecidableEq I] (N : ℕ) (hN : N ≠ 0)
    (F : I → subfieldEntireFunctionAlgebra k)
    (Z : (Matrix I I (LaurentLogBase k))ˣ) (j : I) :
    stage33_scalarNormalFormRow k N hN F Z j =
      stage38_logAmbient (∑ i, Polynomial.C (stage14_subfieldEntireLaurentAlgHom k
        (stage17_arithmeticPowerPullback k N hN (F i))) *
        laurentLogToSeriesPolynomial (Z.val i j)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  rfl
end StrictEUnit
end
