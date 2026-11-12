import FallingSymbolIntegralDilations

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The actual integer least common multiple of 1,...,N; no growth estimate is
built into this definition. -/
def logJetLCM : ℕ → ℕ
  | 0 => 1
  | N+1 => Nat.lcm (N+1) (logJetLCM N)

theorem logJetLCM_pos (N : ℕ) : 0<logJetLCM N := by
  induction N with
  | zero => exact Nat.zero_lt_one
  | succ N ih => exact Nat.lcm_pos (by omega) ih

theorem logJetLCM_dvd (N k : ℕ) (hk : 0<k) (hkN : k≤N) : k∣logJetLCM N := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases he : k=N+1
    · subst k;exact Nat.dvd_lcm_left _ _
    · exact (ih (by omega)).trans (Nat.dvd_lcm_right _ _)

theorem logJetLCM_dvd_iff (N L : ℕ) : logJetLCM N∣L ↔ ∀ k,0<k → k≤N → k∣L := by
  constructor
  · intro h k hk hkN;exact (logJetLCM_dvd N k hk hkN).trans h
  · intro h
    induction N with
    | zero => exact one_dvd _
    | succ N ih =>
      exact Nat.lcm_dvd (h (N+1) (by omega) le_rfl)
        (ih (fun k hk hkN => h k hk (by omega)))

theorem normalizedFallingSymbol_translate_dilate_integral (x D : K) (L N m : ℕ)
    (hm : m≤N) (hL : ∀ k,0<k → k≤N → k∣L)
    (hD : ∀ a,a≤N → IsIntegral ℤ (D*Ring.choose x a)) :
    ∀ j,IsIntegral ℤ ((Polynomial.C D*
      (normalizedFallingSymbol (K:=K) m).comp (Polynomial.C (L : K)*Polynomial.X+Polynomial.C x)).coeff j) := by
  have hid : (normalizedFallingSymbol (K:=K) m).comp (Polynomial.C (L : K)*Polynomial.X+Polynomial.C x)=
      ∑ ab ∈ Finset.antidiagonal m,Polynomial.C (Ring.choose x ab.1)*
        (normalizedFallingSymbol (K:=K) ab.2).comp (Polynomial.C (L : K)*Polynomial.X) := by
    have h := congrArg (fun P : Polynomial K => P.comp (Polynomial.C (L : K)*Polynomial.X))
      (normalizedFallingSymbol_translate x m)
    simpa only [Polynomial.comp_assoc,Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp,
      Polynomial.sum_comp,Polynomial.mul_comp] using h
  rw [hid,Finset.mul_sum]
  intro j
  rw [Polynomial.finset_sum_coeff]
  apply IsIntegral.sum
  rintro ⟨a,b⟩ hab
  have hab' := Finset.mem_antidiagonal.mp hab
  rw [← mul_assoc,← Polynomial.C_mul,Polynomial.coeff_C_mul]
  exact (hD a (by omega)).mul (normalizedFallingSymbol_integral_dilation L N b (by omega) hL j)

/-- One binomial denominator per factor and only L^j for jet degree j.
The LCM exponent does not multiply by the number of filters. -/
theorem fallingCompositeSymbol_logJet_integral {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (alpha D : K) (N L : ℕ)
    (hm : ∀ i,ms i≤N) (hL : ∀ k,0<k → k≤N → k∣L)
    (hD : ∀ a,a≤N → ∀ i,IsIntegral ℤ (D*Ring.choose (alpha-rho (u i)) a)) (j : ℕ) :
    IsIntegral ℤ (D^q*(L : K)^j*((fallingCompositeSymbol rho u ms).comp
      (Polynomial.X+Polynomial.C alpha)).coeff j) := by
  classical
  let P := (fallingCompositeSymbol rho u ms).comp (Polynomial.X+Polynomial.C alpha)
  have hid : Polynomial.C (D^q)*(P.comp (Polynomial.C (L : K)*Polynomial.X))=
      ∏ i : Fin q,Polynomial.C D*(normalizedFallingSymbol (K:=K) (ms i)).comp
        (Polynomial.C (L : K)*Polynomial.X+Polynomial.C (alpha-rho (u i))) := by
    apply Polynomial.funext
    intro x
    simp only [P,fallingCompositeSymbol,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_prod,
      Polynomial.eval_sub,Polynomial.eval_pow,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    ring
  have hi : ∀ k,IsIntegral ℤ ((Polynomial.C (D^q)*(P.comp (Polynomial.C (L : K)*Polynomial.X))).coeff k) := by
    rw [hid]
    apply polynomial_integral_coeff_prod
    intro i hi
    exact normalizedFallingSymbol_translate_dilate_integral (alpha-rho (u i)) D L N (ms i)
      (hm i) hL (fun a ha => hD a ha i)
  have h := hi j
  rw [Polynomial.coeff_C_mul,Polynomial.comp_C_mul_X_coeff] at h
  convert h using 1 <;> ring

/-- A single e=D^q*LCM(N)^d clears the WHOLE bounded-log jet, uniformly in the
natural target shift n. Only the original exponent-difference binomials enter. -/
theorem fallingCompositeSymbol_logJet_common {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (v : ι) (D N n d : ℕ)
    (hm : ∀ i,ms i≤N)
    (hD : ∀ a,a≤N → ∀ w,IsIntegral ℤ ((D : K)*Ring.choose (rho v-rho w) a)) :
    ∀ j,j≤d → IsIntegral ℤ (((D^q*logJetLCM N^d : ℕ) : K)*
      ((fallingCompositeSymbol rho u ms).comp (Polynomial.X+Polynomial.C (rho v+(n : K)))).coeff j) := by
  intro j hj
  have h := fallingCompositeSymbol_logJet_integral rho u ms (rho v+(n : K)) (D : K)
    N (logJetLCM N) hm (logJetLCM_dvd N)
    (by intro a ha i;rw [show rho v+(n : K)-rho (u i)=(rho v-rho (u i))+(n : K) by ring]
        exact binomial_nat_translate_cleared _ _ N (fun k hk => hD k hk (u i)) n a ha) j
  have hx := (ordinaryJet_natCast_integral (K:=K) (logJetLCM N)).pow (d-j)
  convert h.mul hx using 1
  push_cast
  have he : (logJetLCM N : K)^d=(logJetLCM N : K)^j*(logJetLCM N : K)^(d-j) := by
    rw [← pow_add,Nat.add_sub_of_le hj]
  rw [he]
  ring

end StrictEUnit
end
