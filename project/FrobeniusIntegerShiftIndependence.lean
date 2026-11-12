import FrobeniusAmplitudeBlockIndependence
import Mathlib.Data.Finset.Max

/-!
# Independence after actual integer Laurent shifts

A lowest nonzero Laurent coefficient separates every finite family with
injective pairs (integer shift, logarithmic seed order). In particular this
handles different exponents in a common integral resonance class after they
are put over one external base exponent. The monomial shifts are literal
members of K((z))[log], including negative shifts. No fractional powers,
rationality, arithmetic or analytic convergence is assumed or asserted.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Multiplication by the actual integer Laurent monomial z^s. -/
def frobeniusIntegerShift (s : ℤ) (p : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  Polynomial.C (HahnSeries.single s (1 : K)) * p

theorem frobeniusIntegerShift_coeff (s n : ℤ)
    (p : Polynomial (LaurentSeries K)) (k : ℕ) :
    ((frobeniusIntegerShift s p).coeff k).coeff n = (p.coeff k).coeff (n-s) := by
  rw [frobeniusIntegerShift, Polynomial.coeff_C_mul]
  have h := HahnSeries.coeff_single_mul_add (r := (1 : K))
    (x := p.coeff k) (a := n-s) (b := s)
  simpa only [sub_add_cancel, one_mul] using h

variable [CharZero K]

theorem polynomialLogFrobeniusAmplitude_negative_coeff
    (B : ℕ → Polynomial K) (rho : K) (u : Polynomial K)
    (n : ℤ) (hn : n < 0) (k : ℕ) :
    ((polynomialLogFrobeniusAmplitude B rho u).coeff k).coeff n = 0 := by
  apply logPolynomial_negative_coeff_of_powerSeries _
    (polynomialLogFrobeniusCoefficient B rho u) _ n hn k
  exact logPolynomialToCoefficientSeries_transpose_powerSeries_mk _ _
    (polynomialLogFrobeniusCoefficient_coeff_eq_zero B rho u)

/-- A coefficientwise proof using the least shift with a nonzero relation
coefficient. Distinct log orders at that shift cannot cancel. -/
theorem polynomialLogFrobeniusAmplitude_integerShift_linearIndependent
    {ι : Type*} [Fintype ι] (B : ℕ → Polynomial K) (rho : ι → K)
    (s : ι → ℤ) (j : ι → ℕ)
    (hinj : Function.Injective (fun i => (s i,j i))) :
    LinearIndependent K (fun i => frobeniusIntegerShift (s i)
      (polynomialLogFrobeniusAmplitude B (rho i) (Polynomial.X ^ j i))) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hci
  let S : Finset ι := Finset.univ.filter (fun k => c k ≠ 0)
  have hS : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hci⟩⟩
  obtain ⟨i0,hi0,hmin⟩ := Finset.exists_min_image S s hS
  have hc0 : c i0 ≠ 0 := (Finset.mem_filter.mp hi0).2
  have hz := congrArg
    (fun p : Polynomial (LaurentSeries K) => (p.coeff (j i0)).coeff (s i0)) hc
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul,
    HahnSeries.coeff_sum, HahnSeries.coeff_smul,
    Polynomial.coeff_zero, HahnSeries.coeff_zero] at hz
  have hlead : ((frobeniusIntegerShift (s i0)
      (polynomialLogFrobeniusAmplitude B (rho i0) (Polynomial.X ^ j i0))).coeff
        (j i0)).coeff (s i0) = 1 := by
    rw [frobeniusIntegerShift_coeff, sub_self, polynomialLogFrobeniusAmplitude_seed_coeff]
    simp
  have hother (k : ι) (hki : k ≠ i0) :
      c k • ((frobeniusIntegerShift (s k)
        (polynomialLogFrobeniusAmplitude B (rho k) (Polynomial.X ^ j k))).coeff
          (j i0)).coeff (s i0) = 0 := by
    by_cases hck : c k = 0
    · simp only [hck,zero_smul]
    have hs : s i0 ≤ s k := hmin k
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k,hck⟩)
    rw [frobeniusIntegerShift_coeff]
    by_cases heq : s k = s i0
    · have hj : j k ≠ j i0 := by
        intro hj
        exact hki (hinj (Prod.ext heq hj))
      rw [heq,sub_self,polynomialLogFrobeniusAmplitude_seed_coeff]
      simp [Polynomial.coeff_X_pow,hj,Ne.symm hj]
    · have hneg : s i0-s k < 0 := sub_neg.mpr (lt_of_le_of_ne hs (Ne.symm heq))
      rw [polynomialLogFrobeniusAmplitude_negative_coeff B (rho k)
        (Polynomial.X ^ j k) _ hneg,smul_zero]
  rw [Finset.sum_eq_single i0 (fun k _ hki => hother k hki)
    (fun h => (h (Finset.mem_univ i0)).elim),hlead,smul_eq_mul,mul_one] at hz
  exact hc0 hz

/-- Integer shifts realizing differences from one base exponent give an
independent actual Laurent-log amplitude family for that resonance class.
The base exponent remains external. -/
theorem sameFourierTwistedAmplitude_resonance_linearIndependent
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K)
    (hf : Stage56FiniteFuchs A)
    {ι : Type*} [Fintype ι]
    (i : ι → frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (hi : Function.Injective i) (ξ : K) (s : ι → ℤ)
    (hs : ∀ k,frobeniusRootSeedExponent _ (i k) = ξ + (s k : K)) :
    LinearIndependent K (fun k =>
      frobeniusIntegerShift (s k) (sameFourierTwistedAmplitude A hf (i k))) := by
  apply polynomialLogFrobeniusAmplitude_integerShift_linearIndependent
  intro k l hkl
  apply hi
  apply frobeniusRootSeedIndex_ext _ _ (congrArg Prod.snd hkl)
  have hshift : s k = s l := congrArg Prod.fst hkl
  rw [hs k,hs l,hshift]

end StrictEUnit
end

#print axioms StrictEUnit.frobeniusIntegerShift_coeff
#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_negative_coeff
#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_integerShift_linearIndependent
#print axioms StrictEUnit.sameFourierTwistedAmplitude_resonance_linearIndependent
