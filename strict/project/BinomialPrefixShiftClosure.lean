import SelectedFourierJointBinomialArithmetic
import Mathlib.RingTheory.Binomial

/-! Arithmetic closure of the already-proved exponent-binomial sequences.
Negation uses an integer triangular transform, not factorial denominator products. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem descPochhammer_int_smeval (x : K) (m : ℕ) :
    (descPochhammer ℤ m).smeval x=(descPochhammer K m).eval x := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [descPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_sub,
      Polynomial.smeval_X,Polynomial.smeval_natCast,pow_one,pow_zero,nsmul_eq_mul,mul_one,
      Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_natCast,ih]

theorem field_choose_eq_descPochhammer_div (x : K) (m : ℕ) :
    Ring.choose x m=(descPochhammer K m).eval x/(m.factorial : K) := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))).2
  have h := Ring.descPochhammer_eq_factorial_smul_choose x m
  rw [descPochhammer_int_smeval,nsmul_eq_mul] at h
  exact (mul_comm _ _).trans h.symm

/-- The same clearing integer for a prefix of binom(x,m) clears binom(-x,m).
There is no extra growth loss. -/
theorem binomial_negative_cleared_prefix (x : K) (D N : ℕ)
    (h : ∀ m,m≤N → IsIntegral ℤ ((D : K)*Ring.choose x m)) :
    ∀ m,m≤N → IsIntegral ℤ ((D : K)*Ring.choose (-x) m) := by
  intro m hm
  cases m with
  | zero => simpa only [Ring.choose_zero_right,mul_one] using ordinaryJet_natCast_integral (K:=K) D
  | succ m =>
    rw [Ring.choose_neg]
    have he : x+((m+1 : ℕ) : K)-1=x+(m : K) := by push_cast; ring
    rw [he,Ring.add_choose_eq _ (Commute.all _ _)]
    rw [show (Int.negOnePow ((m+1 : ℕ) : ℤ) •
      ∑ ab ∈ Finset.antidiagonal (m+1),Ring.choose x ab.1*Ring.choose (m : K) ab.2)=
      ((Int.negOnePow ((m+1 : ℕ) : ℤ) : ℤ) : K)*
        ∑ ab ∈ Finset.antidiagonal (m+1),Ring.choose x ab.1*Ring.choose (m : K) ab.2 from zsmul_eq_mul _ _]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply IsIntegral.sum
    rintro ⟨a,b⟩ hab
    have hab' := Finset.mem_antidiagonal.mp hab
    have ha : a≤N := by omega
    have hh := h a ha
    have hi : IsIntegral ℤ ((Int.negOnePow ((m+1 : ℕ) : ℤ) : ℤ) : K) :=
      isIntegral_algebraMap (R:=ℤ) (A:=K)
    have hn : IsIntegral ℤ (Ring.choose (m : K) b) := by
      rw [Ring.choose_natCast]
      exact ordinaryJet_natCast_integral _
    convert (hi.mul hh).mul hn using 1 <;> ring

theorem jointBinomialPrefixDenominators_neg {ι : Type*} (rho : ι → K)
    (h : JointBinomialPrefixDenominators rho) :
    JointBinomialPrefixDenominators (fun i => -rho i) := by
  obtain ⟨C,hC,hden⟩ := h
  refine ⟨C,hC,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm i
  rw [← field_choose_eq_descPochhammer_div]
  apply binomial_negative_cleared_prefix (rho i) D N _ m hm
  intro a ha
  simpa only [field_choose_eq_descPochhammer_div] using hDi a ha i

/-- Pairwise differences of an entire family have joint binomial arithmetic.
A squared original clearing integer suffices at each cutoff. -/
theorem jointBinomialPrefixDenominators_sub {ι : Type*} (rho : ι → K)
    (h : JointBinomialPrefixDenominators rho) :
    JointBinomialPrefixDenominators (fun ij : ι × ι => rho ij.1-rho ij.2) := by
  obtain ⟨C,hC,hden⟩ := h
  refine ⟨C^2,one_le_pow₀ hC,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D^2,pow_pos hD 2,?_,?_⟩
  · rw [Nat.cast_pow,pow_right_comm]
    exact pow_le_pow_left₀ (Nat.cast_nonneg D) hDb 2
  · intro m hm ij
    change IsIntegral ℤ (((D^2 : ℕ) : K)*((descPochhammer K m).eval (rho ij.1-rho ij.2)/(m.factorial : K)))
    rw [← field_choose_eq_descPochhammer_div,sub_eq_add_neg,Ring.add_choose_eq _ (Commute.all _ _),Finset.mul_sum]
    apply IsIntegral.sum
    rintro ⟨a,b⟩ hab
    have hab' := Finset.mem_antidiagonal.mp hab
    have ha := hDi a (by omega) ij.1
    have hb : IsIntegral ℤ ((D : K)*Ring.choose (-rho ij.2) b) := by
      apply binomial_negative_cleared_prefix (rho ij.2) D N _ b (by omega)
      intro t ht
      simpa only [field_choose_eq_descPochhammer_div] using hDi t ht ij.2
    rw [← field_choose_eq_descPochhammer_div] at ha
    convert ha.mul hb using 1
    push_cast
    ring

end StrictEUnit
end
