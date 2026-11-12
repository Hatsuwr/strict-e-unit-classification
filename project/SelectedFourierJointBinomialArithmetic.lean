import SelectedFourierExponentArithmetic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- One constant and one integer per cutoff for all exponent-binomial
sequences. This is not arithmetic of the Frobenius amplitudes. -/
def JointBinomialPrefixDenominators {K ι : Type*} [Field K] (rho : ι → K) : Prop :=
  ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(N+1) ∧
    ∀ m,m≤N → ∀ j,IsIntegral ℤ
      ((d:K)*((descPochhammer K m).eval (rho j)/(m.factorial:K)))

/-- The finite product uses the actually derived positive denominators;
no uniform arithmetic premise is supplied. -/
theorem finite_binomialPrefixDenominators {K ι : Type*} [Field K] [Fintype ι]
    (rho : ι → K) (h : ∀ j,BinomialPrefixDenominators (rho j)) :
    JointBinomialPrefixDenominators rho := by
  classical
  choose C hC hpre using h
  refine ⟨∏ j,C j,?_,?_⟩
  · simpa using (Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun _ : ι => (1:ℝ)) (g:=C) (fun _ _ => zero_le_one) (fun j _ => hC j))
  · intro N
    choose d hd hdb hint using (fun j => hpre j N)
    refine ⟨∏ j,d j,Finset.prod_pos (fun j _ => hd j),?_,?_⟩
    · rw [Nat.cast_prod]
      exact (Finset.prod_le_prod (fun j _ => Nat.cast_nonneg (d j))
        (fun j _ => hdb j)).trans_eq (Finset.prod_pow Finset.univ (N+1) C)
    · intro m hm j
      obtain ⟨b,hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
      rw [hb,Nat.cast_mul]
      convert (hint j m hm).mul (ordinaryJet_natCast_integral (K:=K) b) using 1 <;> ring

/-- Joint binomial denominators for ANY Fin nu root tuple of the SAME literal
Fourier indicial polynomial, in particular the existing constructed exponents.
No other family or operator is chosen. -/
def SameClearingFourierJointBinomialData
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U
  let p : Fin (n+2) → Polynomial AlgebraicComplex := fun i => (q i).map φ
  let qplus := ordinaryReflectionTuple (n+1) p
  let d := reciprocalCommonDegree (n+1) qplus
  let ν := reciprocalSourceDegree (n+1) d qplus
  let A := reciprocalSourceArray (n+1) d qplus
  ∀ hf : Stage56FiniteFuchs A,∀ rho : Fin ν → AlgebraicComplex,
    (∀ j,(sameFourierEulerCoefficientSymbols A hf 0).eval (rho j)=0) →
      JointBinomialPrefixDenominators rho

theorem sameClearingFourierIndicialArithmeticData_joint
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (hAll : SameClearingFourierIndicialArithmeticData φ n T UI) :
    SameClearingFourierJointBinomialData φ n T UI := by
  intro hf rho hroot
  exact finite_binomialPrefixDenominators rho (fun j => hAll hf (rho j) (hroot j))

end StrictEUnit
end
