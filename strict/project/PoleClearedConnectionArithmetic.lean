import PoleClearedConnectionGerms
import OrdinaryPointConnectionDenominators

/-! Exponential COMMON denominators for full local connection germs at the
original center. No ordinary-center assumption or solution-basis premise. -/
noncomputable section
open scoped NumberField BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem integral_norm_clears_integral_power
    (v : 𝓞 K) (hv : v≠0) (delta N e : ℕ) (he : e≤N) (x : K)
    (hx : IsIntegral ℤ ((delta : K)*(v : K)^e*x)) :
    IsIntegral ℤ (((delta*(Int.natAbs (Algebra.norm ℤ v))^N : ℕ) : K)*x) := by
  have hvK : (v : K)≠0 := by intro h; exact hv (Subtype.ext h)
  have h := ordinaryJet_norm_power_clearing v hv delta N e he ((v : K)^e*x)
    (by simpa only [mul_assoc] using hx)
  convert h using 1
  field_simp [hvK]
  ring

/-- Removing only the original coordinate pole preserves exponential
arithmetic jointly in derivative order and local coefficient degree. -/
theorem poleClearedPolynomialQuotientGerm_common_denominators {ι : Type*}
    (T : Polynomial (𝓞 K)) (H : ℕ → ι → Polynomial K)
    (hT : T.map (algebraMap (𝓞 K) K)≠0) (E : ℝ) (hE : 1≤E)
    (hden : ∀ N : ℕ,∃ delta : ℕ,0<delta ∧ (delta : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N → ∀ i k,IsIntegral ℤ ((delta : K)*(H m i).coeff k)) :
    let t := T.map (algebraMap (𝓞 K) K)
    let v := T.coeff t.natTrailingDegree
    let q := Int.natAbs (Algebra.norm ℤ v)
    0<q ∧ 1≤(q : ℝ)*E ∧
    ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤((q : ℝ)*E)^(N+1) ∧
      ∀ m k,m+k≤N → ∀ i,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K k (poleClearedPolynomialQuotientGerm t (H m i) m)) := by
  intro t v q
  let tau := t.coeff t.natTrailingDegree
  have hvmap : (v : K)=tau := by
    dsimp only [v,tau,t]
    rw [Polynomial.coeff_map]
  have htau : tau≠0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hv : v≠0 := by
    intro hz
    apply htau
    rw [← hvmap,hz]
    rfl
  have hq : 0<q := (ringOfIntegers_natAbs_norm_certificate v hv).1
  have hq1 : (1 : ℝ)≤(q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hqE : 1≤(q : ℝ)*E := by
    simpa only [one_mul] using mul_le_mul hq1 hE zero_le_one (Nat.cast_nonneg q)
  refine ⟨hq,hqE,?_⟩
  intro N
  obtain ⟨delta,hd,hdb,hdi⟩ := hden N
  refine ⟨delta*q^N,Nat.mul_pos hd (pow_pos hq N),
    ordinaryJet_cutoff_norm_bound q delta N hq E hE hdb,?_⟩
  intro m k hmk i
  have hf : ∀ j,IsIntegral ℤ (PowerSeries.coeff K j (sameCompanionEulerDenominatorSeries t)) := by
    intro j
    simp only [sameCompanionEulerDenominatorSeries,polynomialTailPowerSeries,PowerSeries.coeff_mk,
      t,Polynomial.coeff_map]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have hi := powerSeries_cleared_mul_inverse_pow_integral
    (sameCompanionEulerDenominatorSeries t) (H m i : PowerSeries K) tau (delta : K)
    (sameCompanionEulerDenominatorSeries_constantCoeff t) htau hf
    (by intro j; simpa only [Polynomial.coeff_coe] using hdi m (by omega) i j) m k
  apply integral_norm_clears_integral_power v hv delta N (m+k) hmk
  simpa only [hvmap,poleClearedPolynomialQuotientGerm] using hi

/-- A triangular two-index bound supplies a single exponential bound on
rectangular prefixes as well; only a fixed squaring of the base is needed. -/
theorem bivariate_exponential_denominators_rectangular {ι : Type*}
    (x : ℕ → ℕ → ι → K) (C : ℝ) (hC : 1≤C)
    (h : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤C^(N+1) ∧
      ∀ m k,m+k≤N → ∀ i,IsIntegral ℤ ((D : K)*x m k i)) :
    ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤(C^2)^(N+1) ∧
      ∀ m,m≤N → ∀ k,k≤N → ∀ i,IsIntegral ℤ ((D : K)*x m k i) := by
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := h (2*N)
  refine ⟨D,hD,?_,?_⟩
  · apply hDb.trans
    rw [← pow_mul]
    exact pow_le_pow_right₀ hC (by omega)
  · intro m hm k hk i
    exact hDi m k (by omega) i

end StrictEUnit
end
