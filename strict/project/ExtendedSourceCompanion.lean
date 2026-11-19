import ExtendedSourceResidualFrame
import ReciprocalArrayFieldMap

noncomputable section
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

/-- The enlarged-field companion is normalized from the SAME cleared last
row and SAME denominator, not selected from a new annihilator. -/
def extendedSourceCompanion (psi : K →+* L) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (j : Fin (n+1)) : RatFunc L :=
  algebraMap (Polynomial L) (RatFunc L) ((U (Fin.last n) j).map psi)/
    algebraMap (Polynomial L) (RatFunc L) (T.map psi)

theorem extendedSourceCompanion_clearing (psi : K →+* L) (n : ℕ)
    (c : Fin (n+1) →RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j) :
    ∀ i j,algebraMap (Polynomial L) (RatFunc L) ((U i j).map psi)=
      algebraMap (Polynomial L) (RatFunc L) (T.map psi)*
        minimalDerivativeCompanion (n+1) (extendedSourceCompanion psi n T U) i j := by
  classical
  have ht : algebraMap (Polynomial L) (RatFunc L) (T.map psi)≠0 := by
    apply (map_ne_zero_iff _ (RatFunc.algebraMap_injective L)).mpr
    exact (Polynomial.map_ne_zero_iff psi.injective).mpr hT
  intro i j
  cases i using Fin.lastCases with
  | last =>
    simp only [minimalDerivativeCompanion,Fin.val_last,lt_self_iff_false,ite_false,extendedSourceCompanion]
    field_simp
  | cast i =>
    rw [cleared_companion_shift_row n c T U hclear i j]
    have hi : i.val+1<n+1 := by omega
    simp only [minimalDerivativeCompanion,Fin.coe_castSucc,if_pos hi]
    by_cases hj : j=i.succ
    · subst j
      simp [Pi.single_apply]
    · have hval : j.val≠i.val+1 := fun h =>hj (Fin.ext h)
      simp [Pi.single_apply,hj,Ne.symm hj,hval]

theorem extendedSourceCompanion_valuation (psi : K →+* L) (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1)) :
    ∀ j,(U (Fin.last n) j).map psi≠0 →
      (T.map psi).natTrailingDegree+j.val≤((U (Fin.last n) j).map psi).natTrailingDegree+(n+1) := by
  intro j hj
  simpa only [polynomial_natTrailingDegree_map] using
    hV j ((Polynomial.map_ne_zero_iff psi.injective).mp hj)

end StrictEUnit
end
