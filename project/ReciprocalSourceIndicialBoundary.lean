import ReciprocalValuationFuchs
import OrdinaryReflectionValuation
import SelectedScalarFieldMapTransport
import RegularResidueFieldMap
import SameCompanionScalarTuple

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Guarded critical coefficient; negative putative indices contribute zero. -/
def reciprocalSourceBoundaryCoefficient (r t : ℕ)
    (q : Fin (r+1) → Polynomial K) (i : Fin (r+1)) : K :=
  if r≤t+i.val then (q i).coeff (t+i.val-r) else 0

def reciprocalSourceBoundaryIndicial (r : ℕ) (q : Fin (r+1) → Polynomial K) : Polynomial K :=
  ∑ i,Polynomial.C (reciprocalSourceBoundaryCoefficient r
    (q (Fin.last r)).natTrailingDegree q i)*descPochhammer K i.val

theorem reciprocalSourceBoundaryCoefficient_map {L : Type*} [Field L]
    (φ : K →+* L) (r t : ℕ) (q : Fin (r+1) → Polynomial K) (i : Fin (r+1)) :
    reciprocalSourceBoundaryCoefficient r t (fun i => (q i).map φ) i=
      φ (reciprocalSourceBoundaryCoefficient r t q i) := by
  unfold reciprocalSourceBoundaryCoefficient
  split_ifs <;> simp [Polynomial.coeff_map]

theorem reciprocalSourceBoundaryIndicial_map {L : Type*} [Field L]
    (φ : K →+* L) (r : ℕ) (q : Fin (r+1) → Polynomial K) :
    reciprocalSourceBoundaryIndicial r (fun i => (q i).map φ)=
      (reciprocalSourceBoundaryIndicial r q).map φ := by
  simp only [reciprocalSourceBoundaryIndicial,polynomial_natTrailingDegree_map,
    Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,descPochhammer_map,
    reciprocalSourceBoundaryCoefficient_map]

/-- Reflection gives ONE common sign on the entire guarded critical face. -/
theorem reciprocalSourceBoundaryCoefficient_reflection
    (r t : ℕ) (q : Fin (r+1) → Polynomial K) (i : Fin (r+1)) :
    reciprocalSourceBoundaryCoefficient r t (ordinaryReflectionTuple r q) i=
      (-1:K)^(t+r)*reciprocalSourceBoundaryCoefficient r t q i := by
  unfold reciprocalSourceBoundaryCoefficient
  split_ifs with h
  · rw [ordinaryReflectionTuple_coeff]
    have he : (t+i.val-r+i.val)+2*r=(t+r)+2*i.val := by omega
    have hs := congrArg (fun m : ℕ => (-1:K)^m) he
    simp only [pow_add,pow_mul,neg_one_sq,one_pow,mul_one] at hs
    simp only [pow_add]
    rw [hs]
    exact mul_comm _ _
  · simp

theorem reciprocalSourceBoundaryIndicial_reflection
    (r : ℕ) (q : Fin (r+1) → Polynomial K) :
    reciprocalSourceBoundaryIndicial r (ordinaryReflectionTuple r q)=
      Polynomial.C ((-1:K)^((q (Fin.last r)).natTrailingDegree+r))*
        reciprocalSourceBoundaryIndicial r q := by
  simp only [reciprocalSourceBoundaryIndicial,ordinaryReflectionTuple_natTrailingDegree,
    reciprocalSourceBoundaryCoefficient_reflection,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The SAME selected scalar signs and original trailing coefficient give
exactly the existing source residue polynomial, with original T restored. -/
theorem reciprocalSourceBoundaryIndicial_sameCompanion
    (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0) :
    reciprocalSourceBoundaryIndicial (n+1)
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)=
      Polynomial.C (T.coeff T.natTrailingDegree)*
        regularResidueIndicial n (T.coeff T.natTrailingDegree)
          (polynomialCompanionFace n 1 1 T U) := by
  classical
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U
  let t := T.natTrailingDegree
  let τ := T.coeff t
  let β := polynomialCompanionFace n 1 1 T U
  have hidx : (⟨n+1-1,by omega⟩ : Fin (n+1))=Fin.last n := by
    apply Fin.ext
    simp
  have hlo (j : Fin (n+1)) : reciprocalSourceBoundaryCoefficient (n+1) t q j.castSucc= -β j := by
    dsimp only [reciprocalSourceBoundaryCoefficient,q,sameCompanionScalarTuple]
    simp only [Fin.lastCases_castSucc,Fin.coe_castSucc,hidx,Polynomial.coeff_neg]
    dsimp only [β,polynomialCompanionFace]
    simp only [Nat.one_mul,Nat.mul_one,Polynomial.expand_one]
    have hguard : n+1≤t+j.val ↔ n+1-j.val≤T.natTrailingDegree := by
      dsimp only [t]
      have hj := j.isLt
      omega
    simp only [hguard]
    split_ifs
    · congr 1
      congr 1
      dsimp only [t]
      have hj := j.isLt
      omega
    · simp
  have hlast : reciprocalSourceBoundaryCoefficient (n+1) t q (Fin.last (n+1))=τ := by
    simp [reciprocalSourceBoundaryCoefficient,q,sameCompanionScalarTuple,t,τ]
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hs : Polynomial.C τ*(∑ j : Fin (n+1),Polynomial.C (β j/τ)*descPochhammer K j.val)=
      ∑ j : Fin (n+1),Polynomial.C (β j)*descPochhammer K j.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc,← map_mul,mul_div_cancel₀ _ hτ]
  change reciprocalSourceBoundaryIndicial (n+1) q=Polynomial.C τ*regularResidueIndicial n τ β
  unfold reciprocalSourceBoundaryIndicial
  have hqt : q (Fin.last (n+1))=T := by simp [q,sameCompanionScalarTuple]
  rw [hqt]
  change (∑ i : Fin (n+2),Polynomial.C (reciprocalSourceBoundaryCoefficient (n+1) t q i)*
    descPochhammer K i.val)=Polynomial.C τ*regularResidueIndicial n τ β
  rw [Fin.sum_univ_castSucc]
  simp only [hlo,hlast,Fin.coe_castSucc,Fin.val_last,Polynomial.C_neg,neg_mul,
    Finset.sum_neg_distrib,regularResidueIndicial,mul_sub,hs]
  ring

end StrictEUnit
end
