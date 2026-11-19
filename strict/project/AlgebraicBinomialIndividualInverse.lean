import BinomialIndividualInverseBounds
import Stage26FiniteCoefficientField

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

/-- Joint binomial prefix arithmetic reflects along an injective field map. -/
theorem jointBinomialPrefixDenominators_of_map
    {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
    {ι : Type*} (phi : K →+* L) (rho : ι → K)
    (h : JointBinomialPrefixDenominators (fun i => phi (rho i))) :
    JointBinomialPrefixDenominators rho := by
  obtain ⟨B,hB,hden⟩ := h
  refine ⟨B,hB,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm i
  rw [← field_choose_eq_descPochhammer_div]
  apply (isIntegral_algHom_iff phi.toIntAlgHom phi.injective).1
  change IsIntegral ℤ (phi ((D : K)*Ring.choose (rho i) m))
  rw [map_mul,map_natCast,field_choose_map,field_choose_eq_descPochhammer_div]
  exact hDi m hm i

/-- The finite number field used for the inverse certificate is constructed
from the actual finite exponent data. No field-of-definition premise is added. -/
theorem algebraic_binomial_composite_individual_inverse_bounds
    {ι : Type*} [Fintype ι] (rho : ι → AlgebraicComplex)
    (hrho : JointBinomialPrefixDenominators rho) (q : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N n,n≤N → ∀ (u : Fin q → ι) (ms : Fin q → ℕ),
      (∀ i,ms i≤N) →
      (∏ i : Fin q,Ring.choose (rho (u i)+(n : AlgebraicComplex)) (ms i))≠0 →
      ∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧ IsIntegral ℤ ((e : AlgebraicComplex)*
        (∏ i : Fin q,Ring.choose (rho (u i)+(n : AlgebraicComplex)) (ms i))⁻¹) := by
  obtain ⟨E,hE,hFE,hdata⟩ := stage26_finite_coefficient_field_enlarge_polynomials
    (⊥ : IntermediateField ℚ AlgebraicComplex) inferInstance (fun i => Polynomial.C (rho i))
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  have hr (i : ι) : rho i∈E := by simpa only [Polynomial.coeff_C_zero] using hdata i 0
  let r : ι → E := fun i => ⟨rho i,hr i⟩
  have hmap : (fun i => algebraMap E AlgebraicComplex (r i))=rho := rfl
  have hR : JointBinomialPrefixDenominators r :=
    jointBinomialPrefixDenominators_of_map (algebraMap E AlgebraicComplex) r (by rw [hmap];exact hrho)
  obtain ⟨C,hC,hbounds⟩ := binomialCompositeValue_individual_inverse_bounds r hR q
  refine ⟨C,hC,?_⟩
  intro N n hn u ms hm hx
  have hid : algebraMap E AlgebraicComplex (binomialCompositeValue r u ms n)=
      ∏ i : Fin q,Ring.choose (rho (u i)+(n : AlgebraicComplex)) (ms i) := by
    simp only [binomialCompositeValue,map_prod,field_choose_map,map_add,map_natCast]
    rfl
  have hx' : binomialCompositeValue r u ms n≠0 := by
    intro hz
    rw [hz,map_zero] at hid
    exact hx hid.symm
  obtain ⟨e,he,heb,hei⟩ := hbounds N n hn u ms hm hx'
  refine ⟨e,he,heb,?_⟩
  have h := hei.map (algebraMap E AlgebraicComplex).toIntAlgHom
  simpa only [RingHom.toIntAlgHom_apply,map_mul,map_natCast,map_inv₀,hid] using h

/-- Exact specialization to the composite diagonal. These inverse bounds are
individual; they do NOT assert one denominator shared by a growing prefix. -/
theorem algebraic_fallingComposite_diagonal_individual_inverse_bounds
    {ι : Type*} [Fintype ι] (rho : ι → AlgebraicComplex)
    (hrho : JointBinomialPrefixDenominators rho) (q : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N n,n≤N → ∀ (u : Fin q → ι) (ms : Fin q → ℕ),
      (∀ i,ms i≤N) → ∀ v,(fallingCompositeSymbol rho u ms).eval (rho v+(n : AlgebraicComplex))≠0 →
      ∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧ IsIntegral ℤ ((e : AlgebraicComplex)*
        ((fallingCompositeSymbol rho u ms).eval (rho v+(n : AlgebraicComplex)))⁻¹) := by
  obtain ⟨C,hC,hbound⟩ := algebraic_binomial_composite_individual_inverse_bounds
    (fun ij : ι×ι => rho ij.1-rho ij.2) (jointBinomialPrefixDenominators_sub rho hrho) q
  refine ⟨C,hC,?_⟩
  intro N n hn u ms hm v hx
  rw [fallingCompositeSymbol_diagonal] at hx ⊢
  exact hbound N n hn (fun i => (v,u i)) ms hm hx

end StrictEUnit
end
