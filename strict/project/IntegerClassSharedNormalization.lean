import IntegerBinomialSharedInverse
import FallingLogNormalizationBounds

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Filters from one explicitly presented integer-shift class. There is no
assertion that arbitrary Fourier exponents belong to the same class. -/
def integerClassFallingComposite (rho : K) {q : ℕ} (s : Fin q → ℤ)
    (ms : Fin q → ℕ) : Polynomial K :=
  fallingCompositeSymbol (fun i => rho+(s i : K)) id ms

theorem integerClassFallingComposite_diagonal (rho : K) {q : ℕ}
    (s : Fin q → ℤ) (ms : Fin q → ℕ) (a : ℤ) :
    (integerClassFallingComposite rho s ms).eval (rho+(a : K))=
      ∏ i : Fin q,Ring.choose ((a-s i : ℤ) : K) (ms i) := by
  simp only [integerClassFallingComposite,fallingCompositeSymbol,Polynomial.eval_prod,
    Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    normalizedFallingSymbol_eval,id_eq,Int.cast_sub]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

theorem integerClassFallingComposite_logJet (rho : K) {q : ℕ}
    (s : Fin q → ℤ) (ms : Fin q → ℕ) (a : ℤ) (N d : ℕ)
    (hm : ∀ i,ms i≤N) :
    ∀ j,j≤d → IsIntegral ℤ (((logJetLCM N^d : ℕ) : K)*
      ((integerClassFallingComposite rho s ms).comp
        (Polynomial.X+Polynomial.C (rho+(a : K)))).coeff j) := by
  intro j hj
  have h := fallingCompositeSymbol_logJet_integral (fun i => rho+(s i : K)) id ms
    (rho+(a : K)) 1 N (logJetLCM N) hm (logJetLCM_dvd N)
    (by intro k hk i
        rw [one_mul,show rho+(a : K)-(rho+(s (id i) : K))=((a-s i : ℤ) : K) by simp only [id_eq,Int.cast_sub];ring]
        exact resonance_integer_choose_integral _ _) j
  simp only [one_pow,one_mul] at h
  have he : (logJetLCM N : K)^d=(logJetLCM N : K)^j*(logJetLCM N : K)^(d-j) := by
    rw [← pow_add,Nat.add_sub_of_le hj]
  convert h.mul ((ordinaryJet_natCast_integral (K:=K) (logJetLCM N)).pow (d-j)) using 1
  rw [Nat.cast_pow,he]
  dsimp only [integerClassFallingComposite]
  ring

/-- An explicit COMMON normalizer for all nonzero integer-class pivots in
one bounded prefix, including negative relative target indices. -/
theorem integerClassFallingComposite_lcm_normalization (q d N : ℕ)
    (rho : K) (s : Fin q → ℤ) (ms : Fin q → ℕ) (a : ℤ)
    (hsize : ∀ i,(a-s i).natAbs+ms i≤N)
    (hpivot : (integerClassFallingComposite rho s ms).eval (rho+(a : K))≠0)
    (Z : K) (f : Polynomial K) (hf : f.natDegree≤d)
    (hforced : ∀ j,IsIntegral ℤ (Z*(shiftedPolynomialDifferentialOperator (rho+(a : K))
      (integerClassFallingComposite rho s ms) f).coeff j)) :
    ∀ j,IsIntegral ℤ (((logJetLCM N^((d+q)*(d+1)) : ℕ) : K)*Z*f.coeff j) := by
  have hi := resonance_integer_products_inverse_lcm (K:=K) N q (fun i => a-s i) ms hsize
    (by simpa only [integerClassFallingComposite_diagonal] using hpivot)
  rw [← integerClassFallingComposite_diagonal rho s ms a] at hi
  have h := shiftedPolynomialDifferentialEquation_integer_normalization
    (integerClassFallingComposite rho s ms) f (rho+(a : K)) Z
    (logJetLCM N^d) (logJetLCM N^q) d (pow_pos (logJetLCM_pos N) _) hpivot hf
    (integerClassFallingComposite_logJet rho s ms a N d (fun i => by have := hsize i;omega)) hi hforced
  simpa only [← pow_add,← pow_mul] using h

/-- One exponential denominator is chosen BEFORE the base exponent, all
bounded integer offsets, all target indices, orders and forcing polynomials.
Nonzero pivots remain an explicit necessary condition. -/
theorem integerClassFallingComposite_shared_normalization (q d W : ℕ) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤B^(N+1) ∧
      ∀ (rho : K) (s : Fin q → ℤ),(∀ i,(s i).natAbs≤W) →
        ∀ a : ℤ,a.natAbs≤N+W → ∀ ms : Fin q → ℕ,(∀ i,ms i≤N) →
          (integerClassFallingComposite rho s ms).eval (rho+(a : K))≠0 →
          ∀ (Z : K) (f : Polynomial K),f.natDegree≤d →
            (∀ j,IsIntegral ℤ (Z*(shiftedPolynomialDifferentialOperator (rho+(a : K))
              (integerClassFallingComposite rho s ms) f).coeff j)) →
            ∀ j,IsIntegral ℤ ((e : K)*Z*f.coeff j) := by
  let r := (d+q)*(d+1)
  refine ⟨(16 : ℝ)^((2+2*W)*r),one_le_pow₀ (by norm_num),?_⟩
  intro N
  refine ⟨logJetLCM (2*N+2*W)^r,pow_pos (logJetLCM_pos _) _,?_,?_⟩
  · rw [Nat.cast_pow]
    calc
      (logJetLCM (2*N+2*W) : ℝ)^r≤((16 : ℝ)^(2*N+2*W))^r :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (logJetLCM_real_le_sixteen_pow _) r
      _ ≤((16 : ℝ)^((2+2*W)*r))^(N+1) := by
        rw [← pow_mul,← pow_mul]
        apply pow_le_pow_right₀ (by norm_num)
        calc
          (2*N+2*W)*r≤((2+2*W)*(N+1))*r := Nat.mul_le_mul_right r (by nlinarith)
          _ = (2+2*W)*r*(N+1) := by ring
  · intro rho s hs a ha ms hm hpivot Z f hf hforced j
    apply integerClassFallingComposite_lcm_normalization q d (2*N+2*W) rho s ms a _ hpivot Z f hf hforced j
    intro i
    have h := Int.natAbs_sub_le a (s i)
    have hi := hs i
    have hmi := hm i
    omega

end StrictEUnit
end
