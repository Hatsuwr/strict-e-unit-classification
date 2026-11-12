import EulerCyclicCompanionIdentity

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The scalar-Euler-jet to original-coordinate change is itself triangular,
not merely an unspecified inverse with nonzero determinant. -/
theorem eulerCyclicJetMatrix_inverse_lowerTriangular {n : ℕ}
    (C : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K))
    (hC : ∀ i j,i.val+1<j.val →C i j=0)
    (hp : ∀ i : Fin n,IsUnit (C i.castSucc i.succ)) :
    (∀ i j,i.val<j.val →(eulerCyclicJetMatrix C)⁻¹ i j=0) ∧
      IsUnit ((eulerCyclicJetMatrix C)⁻¹).det := by
  have hdet := eulerCyclicJetMatrix_det_isUnit C hC hp
  letI : Invertible (eulerCyclicJetMatrix C) :=
    ((eulerCyclicJetMatrix C).isUnit_iff_isUnit_det.mpr hdet).nonempty_invertible.some
  have ht : (eulerCyclicJetMatrix C).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact eulerCyclicRow_support C hC i.val j hij
  have hi := Matrix.blockTriangular_inv_of_blockTriangular ht
  exact ⟨fun i j hij =>hi hij,Matrix.isUnit_nonsing_inv_det _ hdet⟩

end StrictEUnit
end
