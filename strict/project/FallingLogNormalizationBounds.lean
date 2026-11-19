import AlgebraicBinomialIndividualInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Converts the bounded-log pivot certificate to an integer normalization
using an explicit integral inverse-pivot multiple. -/
theorem shiftedPolynomialDifferentialEquation_integer_normalization
    (P f : Polynomial K) (alpha D : K) (e b d : ℕ) (he : 0<e)
    (hpivot : P.eval alpha≠0) (hf : f.natDegree≤d)
    (hjet : ∀ j,j≤d → IsIntegral ℤ ((e : K)*
      (P.comp (Polynomial.X+Polynomial.C alpha)).coeff j))
    (hinv : IsIntegral ℤ ((b : K)*(P.eval alpha)⁻¹))
    (hforced : ∀ j,IsIntegral ℤ (D*(shiftedPolynomialDifferentialOperator alpha P f).coeff j)) :
    ∀ j,IsIntegral ℤ ((((e*b)^(d+1) : ℕ) : K)*D*f.coeff j) := by
  intro j
  have h := shiftedPolynomialDifferentialEquation_lowJet_pivot_clearing
    P f alpha D e d he hpivot hf hjet hforced j
  convert h.mul (hinv.pow (d+1)) using 1
  push_cast
  field_simp
  ring

/-- A single block normalizer, uniform over its forcing/log coefficients, has
an explicit exponential-times-LCM bound. It is chosen AFTER the block/pivot;
no common growing-prefix inverse denominator is asserted. -/
theorem algebraic_fallingComposite_logNormalization_bound
    {ι : Type*} [Fintype ι] (rho : ι → AlgebraicComplex)
    (hrho : JointBinomialPrefixDenominators rho) (q d : ℕ) :
    ∃ B : ℝ,1≤B ∧ ∀ N n,n≤N → ∀ (u : Fin q → ι) (ms : Fin q → ℕ),
      (∀ i,ms i≤N) → ∀ v,(fallingCompositeSymbol rho u ms).eval (rho v+(n : AlgebraicComplex))≠0 →
      ∃ e : ℕ,0<e ∧ (e : ℝ)≤B^(N+1)*(logJetLCM N : ℝ)^(d*(d+1)) ∧
        ∀ (D : AlgebraicComplex) (f : Polynomial AlgebraicComplex),f.natDegree≤d →
          (∀ j,IsIntegral ℤ (D*(shiftedPolynomialDifferentialOperator (rho v+(n : AlgebraicComplex))
            (fallingCompositeSymbol rho u ms) f).coeff j)) →
          ∀ j,IsIntegral ℤ ((e : AlgebraicComplex)*D*f.coeff j) := by
  obtain ⟨H,hH,hden⟩ := jointBinomialPrefixDenominators_sub rho hrho
  obtain ⟨C,hC,hinverse⟩ := algebraic_fallingComposite_diagonal_individual_inverse_bounds rho hrho q
  refine ⟨(H^q*C)^(d+1),one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) hC),?_⟩
  intro N n hn u ms hm v hpivot
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  obtain ⟨b,hb,hbb,hbi⟩ := hinverse N n hn u ms hm v hpivot
  let a := D^q*logJetLCM N^d
  have ha : 0<a := Nat.mul_pos (pow_pos hD _) (pow_pos (logJetLCM_pos N) _)
  have hjet := fallingCompositeSymbol_logJet_common rho u ms v D N n d hm
    (by intro k hk w;rw [field_choose_eq_descPochhammer_div];exact hDi k hk (v,w))
  refine ⟨(a*b)^(d+1),pow_pos (Nat.mul_pos ha hb) _,?_,?_⟩
  · have hd : (D : ℝ)^q≤(H^q)^(N+1) := by
      calc
        (D : ℝ)^q≤(H^(N+1))^q := pow_le_pow_left₀ (Nat.cast_nonneg _) hDb q
        _ = (H^q)^(N+1) := by rw [← pow_mul,← pow_mul];congr 1;ring
    have hmul : (D : ℝ)^q*(b : ℝ)≤(H^q*C)^(N+1) := by
      rw [mul_pow]
      exact mul_le_mul hd hbb (Nat.cast_nonneg _) (pow_nonneg (pow_nonneg (le_trans zero_le_one hH) _) _)
    dsimp only [a]
    push_cast
    calc
      ((D : ℝ)^q*(logJetLCM N : ℝ)^d*(b : ℝ))^(d+1) ≤
          ((H^q*C)^(N+1)*(logJetLCM N : ℝ)^d)^(d+1) := by
        apply pow_le_pow_left₀ (by positivity)
        convert mul_le_mul_of_nonneg_right hmul
          (pow_nonneg (Nat.cast_nonneg (logJetLCM N) : (0 : ℝ)≤(logJetLCM N : ℝ)) d) using 1 <;> ring
      _ = ((H^q*C)^(d+1))^(N+1)*(logJetLCM N : ℝ)^(d*(d+1)) := by
        rw [mul_pow,← pow_mul,← pow_mul,← pow_mul]
        congr 1
        congr 1
        ring
  · intro Z f hf hforced j
    exact shiftedPolynomialDifferentialEquation_integer_normalization _ f _ Z a b d ha hpivot hf hjet hbi hforced j

end StrictEUnit
end
