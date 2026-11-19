import ReciprocalGaugeCoefficients
import FocusedFourierNormalizationCore
import Mathlib.RingTheory.Polynomial.Pochhammer

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

def reciprocalGaugeIndicialCoefficient (i k : ℕ) : K :=
  (reciprocalGaugeCoefficient (K := K) i k).coeff (i+k+1)

@[simp] theorem reciprocalGaugeIndicialCoefficient_zero_zero :
    reciprocalGaugeIndicialCoefficient (K := K) 0 0=1 := by
  simp [reciprocalGaugeIndicialCoefficient,reciprocalGaugeCoefficient]

theorem reciprocalGaugeIndicialCoefficient_above (i k : ℕ) (hik : i<k) :
    reciprocalGaugeIndicialCoefficient (K := K) i k=0 := by
  rw [reciprocalGaugeIndicialCoefficient,reciprocalGaugeCoefficient_above i k hik,
    Polynomial.coeff_zero]

theorem reciprocalGaugeIndicialCoefficient_succ (i k : ℕ) :
    reciprocalGaugeIndicialCoefficient (K := K) (i+1) k=
      -((i+k+1:ℕ):K)*reciprocalGaugeIndicialCoefficient i k-
        (if k=0 then 0 else reciprocalGaugeIndicialCoefficient i (k-1)) := by
  have htwo : 2 ≤ i+1+k+1 := by omega
  have hsub : i+1+k+1-2=i+k := by omega
  rw [reciprocalGaugeIndicialCoefficient,reciprocalGaugeCoefficient,neg_mul,
    Polynomial.coeff_sub,Polynomial.coeff_neg,Polynomial.coeff_X_pow_mul',
    if_pos htwo,hsub,Polynomial.coeff_derivative,
    Polynomial.coeff_X_pow_mul',if_pos htwo,hsub]
  by_cases hk : k=0
  · subst k
    simp only [if_true,Polynomial.coeff_zero,sub_zero,
      reciprocalGaugeIndicialCoefficient,Nat.add_zero,Nat.cast_add,Nat.cast_one]
    ring
  · rw [if_neg hk,if_neg hk]
    have hprev : i+(k-1)+1=i+k := by omega
    simp only [reciprocalGaugeIndicialCoefficient,hprev,Nat.cast_add,Nat.cast_one]
    ring

def reciprocalGaugeIndicialKernel (i : ℕ) : Polynomial K :=
  ∑ k : Fin (i+1),
    Polynomial.C (((-1:K)^k.val)*reciprocalGaugeIndicialCoefficient i k.val)*
      ((ascPochhammer K k.val).comp (Polynomial.X+1))

theorem reciprocalGaugeIndicialKernel_succ (i : ℕ) :
    reciprocalGaugeIndicialKernel (K := K) (i+1)=
      (Polynomial.X-Polynomial.C (i:K))*reciprocalGaugeIndicialKernel i := by
  classical
  let A (k : ℕ) : Polynomial K :=
    (ascPochhammer K k).comp (Polynomial.X+1)
  have hA (k : ℕ) : A (k+1)=A k*(Polynomial.X+Polynomial.C ((k+1:ℕ):K)) := by
    dsimp only [A]
    rw [ascPochhammer_succ_right,Polynomial.mul_comp,Polynomial.add_comp,
      Polynomial.X_comp,Polynomial.natCast_comp]
    simp only [Nat.cast_add,Nat.cast_one,Polynomial.C_add,map_one,
      Polynomial.C_eq_natCast]
    ring
  have hfirst :
      (∑ k : Fin (i+2),Polynomial.C (((-1:K)^k.val)*
        (-((i+k.val+1:ℕ):K)*reciprocalGaugeIndicialCoefficient i k.val))*A k.val)=
      ∑ k : Fin (i+1),Polynomial.C (((-1:K)^k.val)*
        (-((i+k.val+1:ℕ):K)*reciprocalGaugeIndicialCoefficient i k.val))*A k.val := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last,
      reciprocalGaugeIndicialCoefficient_above i (i+1) (by omega),
      mul_zero,Polynomial.C_0,zero_mul,add_zero]
  have hsecond :
      (∑ k : Fin (i+2),Polynomial.C (((-1:K)^k.val)*
        (if k.val=0 then 0 else reciprocalGaugeIndicialCoefficient i (k.val-1)))*A k.val)=
      ∑ k : Fin (i+1),Polynomial.C (((-1:K)^(k.val+1))*
        reciprocalGaugeIndicialCoefficient i k.val)*A (k.val+1) := by
    rw [Fin.sum_univ_succ]
    simp
  have hsplit :
      (∑ k : Fin (i+2),Polynomial.C (((-1:K)^k.val)*
        reciprocalGaugeIndicialCoefficient (i+1) k.val)*A k.val)=
      (∑ k : Fin (i+2),Polynomial.C (((-1:K)^k.val)*
        (-((i+k.val+1:ℕ):K)*reciprocalGaugeIndicialCoefficient i k.val))*A k.val)-
      (∑ k : Fin (i+2),Polynomial.C (((-1:K)^k.val)*
        (if k.val=0 then 0 else reciprocalGaugeIndicialCoefficient i (k.val-1)))*A k.val) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [reciprocalGaugeIndicialCoefficient_succ]
    simp only [mul_sub,Polynomial.C_sub,sub_mul]
  change (∑ k : Fin (i+2),
      Polynomial.C (((-1:K)^k.val)*reciprocalGaugeIndicialCoefficient (i+1) k.val)*A k.val)=
    (Polynomial.X-Polynomial.C (i:K))*
      ∑ k : Fin (i+1),Polynomial.C (((-1:K)^k.val)*reciprocalGaugeIndicialCoefficient i k.val)*A k.val
  rw [hsplit,hfirst,hsecond,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hA]
  simp only [pow_succ,Nat.cast_add,Nat.cast_one,map_mul,map_neg,map_add,map_one]
  ring

/-- No extra overall sign or argument shift is present. -/
theorem reciprocalGaugeIndicialKernel_eq_descPochhammer (i : ℕ) :
    reciprocalGaugeIndicialKernel (K := K) i=descPochhammer K i := by
  induction i with
  | zero =>
    simp [reciprocalGaugeIndicialKernel,reciprocalGaugeIndicialCoefficient,
      reciprocalGaugeCoefficient]
  | succ i ih =>
    rw [reciprocalGaugeIndicialKernel_succ,ih,descPochhammer_succ_right,
      Polynomial.C_eq_natCast,mul_comm]

/-- Map the integral falling/rising identity, without a characteristic premise. -/
theorem descPochhammer_comp_add_length (k : ℕ) :
    (descPochhammer K k).comp (Polynomial.X+Polynomial.C (k:K))=
      (ascPochhammer K k).comp (Polynomial.X+1) := by
  have hfall : descPochhammer K k=
      (ascPochhammer K k).comp (Polynomial.X-(k:Polynomial K)+1) := by
    have h := congrArg (Polynomial.map (Int.castRingHom K))
      (descPochhammer_eq_ascPochhammer k)
    simpa only [descPochhammer_map,ascPochhammer_map,Polynomial.map_comp,
      Polynomial.map_add,Polynomial.map_sub,Polynomial.map_X,
      Polynomial.map_natCast,Polynomial.map_one] using h
  rw [hfall,Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.add_comp,Polynomial.sub_comp,Polynomial.X_comp,
    Polynomial.natCast_comp,Polynomial.one_comp,Polynomial.C_eq_natCast]
  ring

/-- Exact critical-diagonal factorization, with argument order k, s. -/
theorem stage61_shiftedDesc_add_factor (k s : ℕ) :
    stage61_shiftedDesc (K := K) k (s+k)=
      descPochhammer K s*((ascPochhammer K k).comp (Polynomial.X+1)) := by
  have hcancel : (Polynomial.X-(k:Polynomial K)).comp
      (Polynomial.X+Polynomial.C (k:K))=Polynomial.X := by
    simp only [Polynomial.sub_comp,Polynomial.X_comp,Polynomial.natCast_comp,
      Polynomial.C_eq_natCast]
    ring
  have h := congrArg (fun P : Polynomial K =>
      P.comp (Polynomial.X+Polynomial.C (k:K))) (descPochhammer_mul K k s)
  simp only [Polynomial.mul_comp,Polynomial.comp_assoc,hcancel,Polynomial.comp_X] at h
  unfold stage61_shiftedDesc
  rw [Nat.add_comm s k,← h,descPochhammer_comp_add_length]
  exact mul_comm _ _

end StrictEUnit
end
