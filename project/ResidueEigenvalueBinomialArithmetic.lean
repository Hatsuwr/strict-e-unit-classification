import RegularEulerResidueArithmetic
import SelectedFourierJointBinomialArithmetic

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A normalized nonzero residue eigenvector transfers matrix-binomial
arithmetic to its ACTUAL eigenvalue. No rationality or scalar arithmetic input. -/
theorem matrixBinomialPrefixArithmetic_eigenvalue {r : ℕ}
    (M : Matrix (Fin r) (Fin r) K) (hM : MatrixBinomialPrefixArithmetic M)
    (xi : K) (v : Fin r →K) (hv : M*ᵥv=xi • v) (k : Fin r) (hk : v k≠0) :
    BinomialPrefixDenominators xi := by
  let w : Fin r →K := (v k)⁻¹ • v
  have hwk : w k=1 := by simp [w,Pi.smul_apply,smul_eq_mul,hk]
  have hw : M*ᵥw=xi • w := by
    rw [show w=(v k)⁻¹ • v from rfl,Matrix.mulVec_smul,hv,smul_smul,smul_smul,mul_comm]
  have hp (m : ℕ) : (∑ j,(matrixFallingProduct M m k j/(m.factorial : K))*w j)=
      (descPochhammer K m).eval xi/(m.factorial : K) := by
    have h := congrFun (matrixFallingProduct_mulVec_eigenvector M w xi hw m) k
    simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,hwk,mul_one] at h
    calc
      _=(∑ j,matrixFallingProduct M m k j*w j)/(m.factorial : K) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj;ring
      _=_ := by rw [h]
  obtain ⟨b,hb,hbi⟩ := exists_positive_nat_integral_vector w
  obtain ⟨B,hB,hden⟩ := hM
  have hb1 : (1 : ℝ)≤(b : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hb
  have hb0 : (0 : ℝ)≤(b : ℝ) := Nat.cast_nonneg b
  refine ⟨(b : ℝ)*B,?_,?_⟩
  · simpa only [one_mul] using mul_le_mul hb1 hB zero_le_one hb0
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden N
    refine ⟨b*D,Nat.mul_pos hb hD,?_,?_⟩
    · rw [Nat.cast_mul,mul_pow]
      exact (mul_le_mul_of_nonneg_left hDb hb0).trans
        (mul_le_mul_of_nonneg_right (le_self_pow₀ hb1 (Nat.succ_ne_zero N))
          (pow_nonneg (le_trans zero_le_one hB) (N+1)))
    · intro m hm
      rw [← hp m,Finset.mul_sum]
      apply IsIntegral.sum
      intro j hj
      convert (hDi m hm k j).mul (hbi j) using 1
      simp only [Nat.cast_mul]
      ring

/-- In particular this arithmetic is forced by the regular connection itself. -/
theorem regularEulerPrefixArithmetic_eigenvalue {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hC : RegularEulerPrefixArithmetic C)
    (xi : K) (v : Fin r →K)
    (hv : (C.map (PowerSeries.constantCoeff K))*ᵥv=xi • v)
    (k : Fin r) (hk : v k≠0) : BinomialPrefixDenominators xi :=
  matrixBinomialPrefixArithmetic_eigenvalue _ hC.residue xi v hv k hk

end StrictEUnit
end
