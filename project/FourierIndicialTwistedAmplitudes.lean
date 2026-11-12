import FocusedFourierNormalizationCore
import PolynomialLogFrobeniusNonzeroAmplitude
import FrobeniusRootSeeds
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem scalarEulerCoefficientSymbol_coeff_fin (r : ℕ) (b : Fin (r+1) → ℕ → K)
    (k : ℕ) (i : Fin (r+1)) : (scalarEulerCoefficientSymbol r b k).coeff i.val=b i k := by
  classical
  simp only [scalarEulerCoefficientSymbol,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ i)).elim

def sameFourierEulerCoefficientSymbols {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A) : ℕ → Polynomial K :=
  scalarEulerCoefficientSymbol ν (fun i k => PowerSeries.coeff K k ((stage61_fourierLift A hf).coeff i.val))

theorem sameFourierEulerIndicial_top {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A) :
    (sameFourierEulerCoefficientSymbols A hf 0).coeff ν=stage61_fourierCorner A := by
  have h := scalarEulerCoefficientSymbol_coeff_fin ν
    (fun i k => PowerSeries.coeff K k ((stage61_fourierLift A hf).coeff i.val)) 0 (Fin.last ν)
  simpa only [sameFourierEulerCoefficientSymbols,Fin.val_last,stage61_fourierLift_top,
    PowerSeries.coeff_C,if_pos rfl] using h

theorem sameFourierEulerIndicial_natDegree {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    (sameFourierEulerCoefficientSymbols A hf 0).natDegree=ν := by
  apply Nat.le_antisymm
  · unfold sameFourierEulerCoefficientSymbols scalarEulerCoefficientSymbol
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [sameFourierEulerIndicial_top]
    exact stage61_fourierCorner_ne_zero A hc

theorem sameFourierEulerIndicial_ne_zero {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) : sameFourierEulerCoefficientSymbols A hf 0 ≠ 0 := by
  intro h
  have hz := sameFourierEulerIndicial_top A hf
  rw [h,Polynomial.coeff_zero] at hz
  exact stage61_fourierCorner_ne_zero A hc hz.symm

variable [CharZero K]

/-- Every actual multiplicity seed has its concrete finite-log amplitude;
its exponent remains external. This is NOT an integer-ramified solution. -/
def sameFourierTwistedAmplitude {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) :
    Polynomial (LaurentSeries K) :=
  polynomialLogFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf)
    (frobeniusRootSeedExponent _ i) (frobeniusRootSeedPolynomial _ i)

theorem sameFourierTwistedAmplitude_nonzero {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) :
    sameFourierTwistedAmplitude A hf i ≠ 0 := by
  apply polynomialLogFrobeniusAmplitude_ne_zero
  exact pow_ne_zero _ Polynomial.X_ne_zero

/-- All resonance terms are solved by the proved polynomial differential
right inverse. Neither rationality nor a nonresonance hypothesis is supplied. -/
theorem sameFourierTwistedAmplitude_equation {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) :
    ∑ k : Fin (ν+1),Polynomial.C (((stage61_fourierLift A hf).coeff k.val):LaurentSeries K)*
      (fun p : Polynomial (LaurentSeries K) => logPolynomialEuler (1:K) p+
        frobeniusRootSeedExponent _ i • p)^[k.val] (sameFourierTwistedAmplitude A hf i)=0 := by
  exact polynomialLogFrobeniusAmplitude_ring_equation ν
    (fun k => (stage61_fourierLift A hf).coeff k.val) _ _
    (sameFourierEulerIndicial_ne_zero A hf hc) (frobeniusRootSeedPolynomial_mem_kernel _ i)

theorem sameFourierTwistedAmplitude_coefficient_equation {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) (m : ℕ) :
    polynomialLogEulerCoefficient (sameFourierEulerCoefficientSymbols A hf)
      (frobeniusRootSeedExponent _ i)
      (polynomialLogFrobeniusCoefficient (sameFourierEulerCoefficientSymbols A hf)
        (frobeniusRootSeedExponent _ i) (frobeniusRootSeedPolynomial _ i)) m=0 :=
  polynomialLogFrobeniusCoefficient_equation _ _ _ (sameFourierEulerIndicial_ne_zero A hf hc)
    (frobeniusRootSeedPolynomial_mem_kernel _ i) m

theorem sameFourierTwistedAmplitude_uniform_log_degree {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) (m : ℕ) :
    (polynomialLogFrobeniusCoefficient (sameFourierEulerCoefficientSymbols A hf)
      (frobeniusRootSeedExponent _ i) (frobeniusRootSeedPolynomial _ i) m).natDegree ≤
        frobeniusRootSeedOrder _ i+ν := by
  simpa only [frobeniusRootSeedPolynomial_natDegree,sameFourierEulerIndicial_natDegree A hf hc]
    using polynomialLogFrobeniusCoefficient_uniform_degree (sameFourierEulerCoefficientSymbols A hf)
      (frobeniusRootSeedExponent _ i) (frobeniusRootSeedPolynomial _ i) m

theorem sameFourierTwistedAmplitude_pair_injective {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A) :
    Function.Injective (fun i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) =>
      (frobeniusRootSeedExponent _ i,sameFourierTwistedAmplitude A hf i)) := by
  intro i j hij
  have hr := congrArg Prod.fst hij
  have hp := congrArg Prod.snd hij
  have hseed : frobeniusRootSeedPolynomial _ i=frobeniusRootSeedPolynomial _ j := by
    ext k
    have h := congrArg (fun p : Polynomial (LaurentSeries K) => (p.coeff k).coeff 0) hp
    unfold sameFourierTwistedAmplitude at h
    dsimp only at h
    have hi := polynomialLogFrobeniusAmplitude_coeff (K:=K) (sameFourierEulerCoefficientSymbols A hf)
      (frobeniusRootSeedExponent _ i) (frobeniusRootSeedPolynomial _ i) k 0
    have hj := polynomialLogFrobeniusAmplitude_coeff (K:=K) (sameFourierEulerCoefficientSymbols A hf)
      (frobeniusRootSeedExponent _ j) (frobeniusRootSeedPolynomial _ j) k 0
    simp only [polynomialLogFrobeniusCoefficient_zero] at hi hj
    exact hi.symm.trans (h.trans hj)
  exact frobeniusRootSeedIndex_polynomial_pair_injective _ (Prod.ext hr hseed)

omit [CharZero K] in
/-- Cardinality is the ACTUAL Fourier order ν, separately from source r.
Distinct exponent-amplitude PAIRS are not yet a represented solution basis. -/
theorem sameFourierTwistedAmplitude_index_card [IsAlgClosed K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    Fintype.card (frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))=ν :=
  frobeniusRootSeedIndex_card_order _ (IsAlgClosed.splits _) ν
    (sameFourierEulerIndicial_natDegree A hf hc)

end StrictEUnit
end
