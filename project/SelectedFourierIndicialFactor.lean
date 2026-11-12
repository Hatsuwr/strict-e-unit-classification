import ReciprocalFourierIndicialBridge
import SelectedScalarFieldMapTransport
import RegularResidueFieldMap

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem regularResidueIndicial_map {L : Type*} [Field L]
    (φ : K →+* L) (n : ℕ) (τ : K) (β : Fin (n+1) → K) :
    (regularResidueIndicial n τ β).map φ=
      regularResidueIndicial n (φ τ) (fun j => φ (β j)) := by
  simp only [regularResidueIndicial,Polynomial.map_sub,Polynomial.map_sum,
    Polynomial.map_mul,Polynomial.map_C,descPochhammer_map,div_eq_mul_inv,map_mul,map_inv₀]

/-- The actual reflected construction has exactly one scalar sign and one
integer-root factor. No source/Fourier spectrum equality is assumed. -/
theorem ordinaryReflection_reciprocalFourierIndicial_factor
    (r : ℕ) (q : Fin (r+1) → Polynomial K) (hq : q (Fin.last r) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds r q) :
    let qplus := ordinaryReflectionTuple r q
    let d := reciprocalCommonDegree r qplus
    let t := (q (Fin.last r)).natTrailingDegree
    let s := d-t+r+1
    let A := reciprocalSourceArray r d qplus
    ∀ hf : Stage56FiniteFuchs A,
      sameFourierEulerCoefficientSymbols A hf 0=
        Polynomial.C ((-1:K)^(s+t+r))*descPochhammer K s*reciprocalSourceBoundaryIndicial r q := by
  intro qplus d t s A hf
  obtain ⟨hplus,hplusreg⟩ := (ordinaryReflectionTuple_last_and_valuation_iff r q).2 ⟨hq,hreg⟩
  have hb : sameFourierEulerCoefficientSymbols A hf 0=
      Polynomial.C ((-1:K)^s)*descPochhammer K s*reciprocalSourceBoundaryIndicial r qplus := by
    have h := reciprocalFourierIndicial_factor r qplus hplus hplusreg
    simpa only [qplus,ordinaryReflectionTuple_natTrailingDegree] using h
  rw [hb,reciprocalSourceBoundaryIndicial_reflection]
  change Polynomial.C ((-1:K)^s)*descPochhammer K s*
      (Polynomial.C ((-1:K)^(t+r))*reciprocalSourceBoundaryIndicial r q)=_
  simp only [pow_add,map_mul]
  ring

/-- Literal factorization for the SAME mapped selected tuple. The regular
bounds are generic inputs here and are discharged by the original source
packet at the selected endpoint. Neither order nor clearing is changed. -/
theorem sameCompanion_mapped_reflected_indicial_factor
    {L : Type*} [Field L] (φ : K →+* L) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hreg : ReciprocalRegularSingularBounds (n+1)
      (fun i => (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U i).map φ)) :
    let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U
    let p : Fin (n+2) → Polynomial L := fun i => (q i).map φ
    let qplus := ordinaryReflectionTuple (n+1) p
    let d := reciprocalCommonDegree (n+1) qplus
    let s := d-T.natTrailingDegree+(n+1)+1
    let A := reciprocalSourceArray (n+1) d qplus
    ∀ hf : Stage56FiniteFuchs A,
      sameFourierEulerCoefficientSymbols A hf 0=
        Polynomial.C (((-1:L)^(s+T.natTrailingDegree+(n+1)))*φ (T.coeff T.natTrailingDegree))*
          descPochhammer L s*regularResidueIndicial n (φ (T.coeff T.natTrailingDegree))
            (fun j => φ (polynomialCompanionFace n 1 1 T U j)) := by
  intro q p qplus d s A hf
  have hq : q (Fin.last (n+1))=T := by simp [q,sameCompanionScalarTuple]
  have hp : p (Fin.last (n+1)) ≠ 0 := by
    change (q (Fin.last (n+1))).map φ ≠ 0
    rw [hq]
    exact (Polynomial.map_ne_zero_iff φ.injective).2 hT
  have ht : (p (Fin.last (n+1))).natTrailingDegree=T.natTrailingDegree := by
    change ((q (Fin.last (n+1))).map φ).natTrailingDegree=T.natTrailingDegree
    rw [hq,polynomial_natTrailingDegree_map]
  have hb : reciprocalSourceBoundaryIndicial (n+1) p=
      Polynomial.C (φ (T.coeff T.natTrailingDegree))*
        regularResidueIndicial n (φ (T.coeff T.natTrailingDegree))
          (fun j => φ (polynomialCompanionFace n 1 1 T U j)) := by
    change reciprocalSourceBoundaryIndicial (n+1) (fun i => (q i).map φ)=_
    rw [reciprocalSourceBoundaryIndicial_map]
    change (reciprocalSourceBoundaryIndicial (n+1)
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)).map φ=_
    rw [reciprocalSourceBoundaryIndicial_sameCompanion n T U hT,
      Polynomial.map_mul,Polynomial.map_C,regularResidueIndicial_map]
  have hfac := ordinaryReflection_reciprocalFourierIndicial_factor (n+1) p hp hreg hf
  rw [ht] at hfac
  change sameFourierEulerCoefficientSymbols A hf 0=
    Polynomial.C ((-1:L)^(s+T.natTrailingDegree+(n+1)))*descPochhammer L s*
      reciprocalSourceBoundaryIndicial (n+1) p at hfac
  rw [hfac,hb]
  simp only [map_mul]
  ring

end StrictEUnit
end
