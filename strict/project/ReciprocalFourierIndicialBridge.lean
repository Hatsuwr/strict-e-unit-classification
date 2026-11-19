import FourierIndicialBoundary
import ReciprocalGaugeIndicialKernel
import ReciprocalSourceIndicialBoundary
import ReciprocalValuationFuchs

/-!
The actual critical Fourier diagonal of the SAME reciprocal source array.
Only the original guarded regular-singular bounds are used. This module
introduces no rational-spectrum, arithmetic, solution-family or infinity
regularity premise. SOURCE ONLY until the separate serial replay.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem polynomial_coeff_mul_at_upper_bounds
    (P Q : Polynomial K) (a b : ℕ)
    (hP : P.natDegree≤a) (hQ : Q.natDegree≤b) :
    (P*Q).coeff (a+b)=P.coeff a*Q.coeff b := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (a,b) ?_ ?_
  · rintro ⟨i,j⟩ hij hne
    have hij' : i+j=a+b := Finset.mem_antidiagonal.mp hij
    by_cases hi : a < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hi),zero_mul]
    by_cases hj : b < j
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hj),mul_zero]
    have heq : (i,j)=(a,b) := Prod.ext (by omega) (by omega)
    exact (hne heq).elim
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim

theorem reciprocalReflect_regular_boundary_degree (r : ℕ)
    (q : Fin (r+1) → Polynomial K) (hreg : ReciprocalRegularSingularBounds r q)
    (i : Fin (r+1)) :
    (Polynomial.reflect (reciprocalCommonDegree r q) (q i)).natDegree≤
      reciprocalCommonDegree r q-(q (Fin.last r)).natTrailingDegree+r-i.val := by
  have htop := le_trans (q (Fin.last r)).natTrailingDegree_le_natDegree
    (reciprocalCommonDegree_bound r q (Fin.last r))
  have hi := i.isLt
  by_cases hqi : q i=0
  · simp only [hqi,Polynomial.reflect_zero,Polynomial.natDegree_zero]
    omega
  · have hb := hreg i hqi
    have hoi := le_trans (q i).natTrailingDegree_le_natDegree (reciprocalCommonDegree_bound r q i)
    exact (reciprocalReflect_natDegree_le _ _ (reciprocalCommonDegree_bound r q i)).trans (by omega)

theorem reciprocalReflect_regular_boundary_coefficient (r : ℕ)
    (q : Fin (r+1) → Polynomial K) (i : Fin (r+1)) :
    (Polynomial.reflect (reciprocalCommonDegree r q) (q i)).coeff
        (reciprocalCommonDegree r q-(q (Fin.last r)).natTrailingDegree+r-i.val)=
      reciprocalSourceBoundaryCoefficient r (q (Fin.last r)).natTrailingDegree q i := by
  have htop := le_trans (q (Fin.last r)).natTrailingDegree_le_natDegree
    (reciprocalCommonDegree_bound r q (Fin.last r))
  have hi := i.isLt
  unfold reciprocalSourceBoundaryCoefficient
  by_cases hg : r≤(q (Fin.last r)).natTrailingDegree+i.val
  · rw [if_pos hg,Polynomial.coeff_reflect,Polynomial.revAt_le (by omega)]
    congr 1
    omega
  · rw [if_neg hg,Polynomial.coeff_reflect,Polynomial.revAt_eq_self_of_lt (by omega)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((reciprocalCommonDegree_bound r q i).trans_lt (by omega))

/-- Exact top diagonal coefficient of every reciprocal derivative row. The
given bound is derived for the original tuple, not a supplied face recurrence. -/
theorem reciprocalSourcePolynomial_regular_boundary (r : ℕ)
    (q : Fin (r+1) → Polynomial K) (hreg : ReciprocalRegularSingularBounds r q) (k : ℕ) :
    (reciprocalSourcePolynomial r (reciprocalCommonDegree r q) q k).coeff
        (reciprocalCommonDegree r q-(q (Fin.last r)).natTrailingDegree+r+1+k)=
      ∑ i : Fin (r+1),
        reciprocalSourceBoundaryCoefficient r (q (Fin.last r)).natTrailingDegree q i*
          reciprocalGaugeIndicialCoefficient i.val k := by
  unfold reciprocalSourcePolynomial
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hidx : reciprocalCommonDegree r q-(q (Fin.last r)).natTrailingDegree+r+1+k=
      (reciprocalCommonDegree r q-(q (Fin.last r)).natTrailingDegree+r-i.val)+(i.val+k+1) := by
    have hit := i.isLt
    omega
  rw [hidx,polynomial_coeff_mul_at_upper_bounds _ _ _ _
    (reciprocalReflect_regular_boundary_degree r q hreg i)
    (reciprocalGaugeCoefficient_natDegree i.val k),
    reciprocalReflect_regular_boundary_coefficient]
  rfl

def fourierBoundaryDiagonalIndex (μ ν : ℕ) (hμν : μ≤ν) (i : Fin (μ+1)) : Fin (ν+1) :=
  ⟨ν-μ+i.val,by have hi := i.isLt;omega⟩

theorem fourierBoundaryIndicial_eq_single_diagonal {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hμν : μ≤ν) :
    fourierBoundaryIndicial A=
      ∑ i : Fin (μ+1),
        Polynomial.C ((-1:K)^(ν-μ+i.val)*A i (fourierBoundaryDiagonalIndex μ ν hμν i))*
          stage61_shiftedDesc i.val (ν-μ+i.val) := by
  classical
  unfold fourierBoundaryIndicial
  apply Finset.sum_congr rfl
  intro i hi
  let j0 := fourierBoundaryDiagonalIndex μ ν hμν i
  have he : stage57_exponent i j0=0 := by
    dsimp [stage57_exponent,j0,fourierBoundaryDiagonalIndex]
    omega
  calc
    (∑ j : Fin (ν+1),if stage57_exponent i j=0 then
        Polynomial.C ((-1:K)^j.val*A i j)*stage61_shiftedDesc i.val j.val else 0)=
      (if stage57_exponent i j0=0 then
        Polynomial.C ((-1:K)^j0.val*A i j0)*stage61_shiftedDesc i.val j0.val else 0) := by
      refine Finset.sum_eq_single j0 ?_ ?_
      · intro j hj hne
        apply if_neg
        intro hzero
        apply hne
        apply Fin.ext
        dsimp only [j0,fourierBoundaryDiagonalIndex]
        unfold stage57_exponent at hzero
        omega
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = _ := by rw [if_pos he];rfl

/-- Extend the finite reciprocal kernel sum only by its proved zero terms. -/
theorem reciprocalGaugeIndicialKernel_sum_fin (r i : ℕ) (hi : i≤r) :
    (∑ k : Fin (r+1),
      Polynomial.C ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i k.val)*
        ((ascPochhammer K k.val).comp (Polynomial.X+1)))=descPochhammer K i := by
  let f (k : ℕ) : Polynomial K :=
    Polynomial.C ((-1:K)^k*reciprocalGaugeIndicialCoefficient i k)*
      ((ascPochhammer K k).comp (Polynomial.X+1))
  rw [← reciprocalGaugeIndicialKernel_eq_descPochhammer i]
  change (∑ k : Fin (r+1),f k.val)=∑ k : Fin (i+1),f k.val
  rw [Fin.sum_univ_eq_sum_range f (r+1),Fin.sum_univ_eq_sum_range f (i+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hi))
  intro k hk hnot
  have hik : i < k := by
    simp only [Finset.mem_range] at hnot
    omega
  dsimp only [f]
  rw [reciprocalGaugeIndicialCoefficient_above i k hik,mul_zero,Polynomial.C_0,zero_mul]

/-- The actual Fourier indicial polynomial factors through the original
source lower face and one explicit integer-root falling polynomial. This is
for the literal reciprocal construction, not an unrelated Fourier operator. -/
theorem reciprocalFourierIndicial_factor (r : ℕ)
    (q : Fin (r+1) → Polynomial K) (hq : q (Fin.last r) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds r q) :
    let d := reciprocalCommonDegree r q
    let t := (q (Fin.last r)).natTrailingDegree
    let s := d-t+r+1
    let A := reciprocalSourceArray r d q
    let hf := reciprocalSourceArray_finiteFuchs r q hq hreg
    sameFourierEulerCoefficientSymbols A hf 0=
      Polynomial.C ((-1:K)^s)*descPochhammer K s*reciprocalSourceBoundaryIndicial r q := by
  classical
  intro d t s A hf
  let ν := reciprocalSourceDegree r d q
  let α : Fin (r+1) → K := reciprocalSourceBoundaryCoefficient r t q
  let V (k : ℕ) : Polynomial K := (ascPochhammer K k).comp (Polynomial.X+1)
  have hν : ν=s+r := by
    dsimp only [ν,d,t,s]
    rw [reciprocalSourceDegree_of_valuations r q hq hreg]
    omega
  have hrν : r≤ν := by omega
  have hsub : ν-r=s := by omega
  have hstart : sameFourierEulerCoefficientSymbols A hf 0=
      ∑ k : Fin (r+1),
        Polynomial.C ((-1:K)^(s+k.val)*(∑ i : Fin (r+1),α i*reciprocalGaugeIndicialCoefficient i.val k.val))*
          stage61_shiftedDesc k.val (s+k.val) := by
    rw [sameFourierEulerIndicial_eq_boundary,fourierBoundaryIndicial_eq_single_diagonal A hrν]
    apply Finset.sum_congr rfl
    intro k hk
    have hc : A k (fourierBoundaryDiagonalIndex r ν hrν k)=
        ∑ i : Fin (r+1),α i*reciprocalGaugeIndicialCoefficient i.val k.val := by
      change (reciprocalSourcePolynomial r d q k.val).coeff (ν-r+k.val)=_
      rw [hsub]
      exact reciprocalSourcePolynomial_regular_boundary r q hreg k.val
    rw [hc]
    change Polynomial.C ((-1:K)^(ν-r+k.val)*
      (∑ i : Fin (r+1),α i*reciprocalGaugeIndicialCoefficient i.val k.val))*
        stage61_shiftedDesc k.val (ν-r+k.val)=_
    rw [hsub]
  have hterm (k : Fin (r+1)) :
      Polynomial.C ((-1:K)^(s+k.val)*(∑ i : Fin (r+1),α i*reciprocalGaugeIndicialCoefficient i.val k.val))*
          stage61_shiftedDesc k.val (s+k.val)=
      Polynomial.C ((-1:K)^s)*descPochhammer K s*
        (∑ i : Fin (r+1),Polynomial.C (α i)*
          (Polynomial.C ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)*V k.val)) := by
    have hC :
        Polynomial.C ((-1:K)^(s+k.val)*(∑ i : Fin (r+1),α i*reciprocalGaugeIndicialCoefficient i.val k.val))=
        Polynomial.C ((-1:K)^s)*
          (∑ i : Fin (r+1),Polynomial.C (α i)*
            Polynomial.C ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)) := by
      calc
        _ = ∑ i : Fin (r+1),Polynomial.C
            (((-1:K)^s*(-1:K)^k.val)*(α i*reciprocalGaugeIndicialCoefficient i.val k.val)) := by
          rw [pow_add,Finset.mul_sum,map_sum]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [map_mul]
          ring
    rw [hC,stage61_shiftedDesc_add_factor]
    change (Polynomial.C ((-1:K)^s)*
        (∑ i : Fin (r+1),Polynomial.C (α i)*Polynomial.C
          ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)))*
        (descPochhammer K s*V k.val)=_
    calc
      _ = Polynomial.C ((-1:K)^s)*descPochhammer K s*
          ((∑ i : Fin (r+1),Polynomial.C (α i)*Polynomial.C
            ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val))*V k.val) := by ring
      _ = _ := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    sameFourierEulerCoefficientSymbols A hf 0=
        ∑ k : Fin (r+1),Polynomial.C ((-1:K)^s)*descPochhammer K s*
          (∑ i : Fin (r+1),Polynomial.C (α i)*
            (Polynomial.C ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)*V k.val)) := by
      rw [hstart]
      exact Finset.sum_congr rfl (fun k hk => hterm k)
    _ = Polynomial.C ((-1:K)^s)*descPochhammer K s*
        (∑ k : Fin (r+1),∑ i : Fin (r+1),Polynomial.C (α i)*
          (Polynomial.C ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)*V k.val)) := by
      rw [Finset.mul_sum]
    _ = Polynomial.C ((-1:K)^s)*descPochhammer K s*
        (∑ i : Fin (r+1),Polynomial.C (α i)*
          (∑ k : Fin (r+1),Polynomial.C
            ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)*V k.val)) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = Polynomial.C ((-1:K)^s)*descPochhammer K s*
        (∑ i : Fin (r+1),Polynomial.C (α i)*descPochhammer K i.val) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∑ k : Fin (r+1),Polynomial.C
          ((-1:K)^k.val*reciprocalGaugeIndicialCoefficient i.val k.val)*V k.val)=
          descPochhammer K i.val from
        reciprocalGaugeIndicialKernel_sum_fin r i.val (Nat.le_of_lt_succ i.isLt)]
    _ = _ := rfl

end StrictEUnit
end
