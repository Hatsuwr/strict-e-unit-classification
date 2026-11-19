import IntegralPivotNormClearing

/-! Positive INTEGER denominator steps for the SAME Fourier Frobenius family.
One fixed scalar clears all shifted symbols; the remaining divisors are exact
powers of integer norms of indicial values. Their cumulative exponential
bound is not assumed or concluded. -/
noncomputable section
open scoped NumberField BigOperators Classical
namespace StrictEUnit

theorem finite_fourier_integer_denominator_steps
    {ι : Type*} [Fintype ι] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν)≠0) (rho : ι → AlgebraicComplex) (seed : ι → ℕ)
    (F : IntermediateField ℚ AlgebraicComplex) (hF : FiniteDimensional ℚ F) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      (∀ i,rho i∈E) ∧ (∀ k j,(sameFourierEulerCoefficientSymbols A hf k).coeff j∈E) ∧
      ∃ b N : ℕ,0<b ∧ 0<N ∧
        (∀ (i : ι) (k s j : ℕ),IsIntegral ℤ ((b : AlgebraicComplex)*
          ((sameFourierEulerCoefficientSymbols A hf k).comp
            (Polynomial.X+Polynomial.C (rho i+(s : AlgebraicComplex)))).coeff j)) ∧
        ∀ (i : ι) (n : ℕ),N≤n →
          ∃ v : 𝓞 E,v≠0 ∧ ((v : E) : AlgebraicComplex)=
            (b : AlgebraicComplex)*(sameFourierEulerCoefficientSymbols A hf 0).eval (rho i+(n : AlgebraicComplex)) ∧
          ∃ q : ℕ,0<q ∧ q=(Int.natAbs (Algebra.norm ℤ v))^(seed i+ν+1) ∧
            ∀ D : AlgebraicComplex,
              (∀ (s : Fin n) (j : ℕ),IsIntegral ℤ (D*(polynomialLogFrobeniusCoefficient
                (sameFourierEulerCoefficientSymbols A hf) (rho i) (Polynomial.X^seed i) s.val).coeff j)) →
              ∀ j,IsIntegral ℤ ((q : AlgebraicComplex)*D*(polynomialLogFrobeniusCoefficient
                (sameFourierEulerCoefficientSymbols A hf) (rho i) (Polynomial.X^seed i) n).coeff j) := by
  let B := sameFourierEulerCoefficientSymbols A hf
  have hP : B 0≠0 := sameFourierEulerIndicial_ne_zero A hf hc
  have hdegree : (B 0).natDegree=ν := sameFourierEulerIndicial_natDegree A hf hc
  letI : Algebra.IsAlgebraic ℤ AlgebraicComplex :=
    (IsFractionRing.comap_isAlgebraic_iff (A:=ℤ) (K:=ℚ) (C:=AlgebraicComplex)).mpr
      (inferInstance : Algebra.IsAlgebraic ℚ AlgebraicComplex)
  obtain ⟨E,hE,hFE,hA,hr,hB,hcoeff,hamp⟩ := finite_fourierFrobenius_coefficient_field A hf rho seed F hF
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  obtain ⟨b,hb,hclear⟩ := finite_fourier_uniform_integral_symbols A hf rho
  have hcuts : ∀ i : ι,∃ N : ℕ,∀ n : ℕ,N≤n → (B 0).eval (rho i+(n : AlgebraicComplex))≠0 :=
    fun i => polynomial_eventually_shifted_nat_nonzero (B 0) hP (rho i)
  choose cut hcut using hcuts
  let N := max 1 (Finset.univ.sup cut)
  refine ⟨E,hE,hFE,hr,hB,b,N, hb,by dsimp [N]; omega,hclear,?_⟩
  intro i n hn
  have hn0 : n≠0 := by have := (le_max_left 1 (Finset.univ.sup cut)).trans hn; omega
  have hnonzero := hcut i n ((Finset.le_sup (f:=cut) (Finset.mem_univ i)).trans
    ((le_max_right _ _).trans hn))
  let pivot := (b : AlgebraicComplex)*(B 0).eval (rho i+(n : AlgebraicComplex))
  have hpivot : pivot≠0 := mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hb)) hnonzero
  have hpivotmem : pivot∈E := by
    apply E.mul_mem (E.natCast_mem b)
    rw [Polynomial.eval_eq_sum]
    apply E.sum_mem
    intro j hj
    exact E.mul_mem (hB 0 j) (E.pow_mem (E.add_mem (hr i) (E.natCast_mem n)) j)
  have hpivotint : IsIntegral ℤ pivot := by
    have h := hclear i 0 n 0
    simpa only [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,zero_add,B,pivot] using h
  let pivotE : E := ⟨pivot,hpivotmem⟩
  have hpivotE : IsIntegral ℤ pivotE :=
    (isIntegral_algHom_iff (E.val.restrictScalars ℤ) E.val.injective).mp hpivotint
  let v : 𝓞 E := ⟨pivotE,hpivotE⟩
  have hv : v≠0 := by
    intro hz
    have h := congrArg (fun x : 𝓞 E => ((x : E) : AlgebraicComplex)) hz
    exact hpivot h
  obtain ⟨q,hq,hqeq,hqbound,hqclear⟩ := integral_pivot_norm_power_clearing E v hv (seed i+ν+1)
  refine ⟨v,hv,rfl,q,hq,hqeq,?_⟩
  intro D hprev j
  have hstep := polynomialLogFrobeniusCoefficient_integral_denominator_step B (rho i)
    (Polynomial.X^seed i) hP b n hb hn0 hnonzero (hclear i) D hprev j
  have hpower : IsIntegral ℤ (pivot^(seed i+ν+1)*(D*(polynomialLogFrobeniusCoefficient
      B (rho i) (Polynomial.X^seed i) n).coeff j)) := by
    simpa only [Polynomial.natDegree_X_pow,hdegree,mul_assoc,pivot] using hstep
  have h := hqclear (D*(polynomialLogFrobeniusCoefficient B (rho i) (Polynomial.X^seed i) n).coeff j) hpower
  simpa only [mul_assoc] using h

end StrictEUnit
end
