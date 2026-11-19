import LogFiniteJetCommonDenominator

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Fixed algebraic frame coordinates cost only a fixed common multiplier.
The indexing k may include log degree and solution/component labels. A separate
alignment step must supply hden for any integer-shifted frame coefficients. -/
theorem finiteFrameCombination_prefix_denominators
    {ι κ : Type*} [Fintype ι] (c : ι →K) (f : ι →ℕ →κ →K)
    (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ i k,IsIntegral ℤ ((D:K)*f i m k)) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ k,IsIntegral ℤ ((D:K)*(∑ i,c i*f i m k)) := by
  classical
  obtain ⟨e,he,hc⟩ := logJet_finite_family_integral c
  have he1 : (1:ℝ)≤e := by exact_mod_cast he
  refine ⟨(e:ℝ)*B,by nlinarith,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨e*D,Nat.mul_pos he hD,?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    have hep : (e:ℝ)≤(e:ℝ)^(N+1) := by
      calc (e:ℝ)=(e:ℝ)^1 := by simp
           _ ≤ (e:ℝ)^(N+1) := pow_le_pow_right₀ he1 (by omega)
    exact mul_le_mul hep hDb (by positivity) (by positivity)
  · intro m hm k
    rw [Finset.mul_sum]
    apply IsIntegral.sum
    intro i hi
    convert (hc i).mul (hDi m hm i k) using 1 <;> push_cast <;> ring

/-- Finitely many fixed shifts preserve exponential common-prefix bounds.
This is a genuine prefix bound, not a product of one-step denominators. -/
theorem finiteFrameShift_prefix_denominators
    {ι κ : Type*} [Fintype ι] (f : ι →ℕ →κ →K) (a : ι →ℕ)
    (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ i k,IsIntegral ℤ ((D:K)*f i m k)) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ i k,IsIntegral ℤ ((D:K)*f i (m+a i) k) := by
  classical
  let A := Finset.univ.sup a
  have ha (i : ι) : a i≤A := Finset.le_sup (f:=a) (Finset.mem_univ i)
  refine ⟨B^(A+1),one_le_pow₀ hB,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden (N+A)
  refine ⟨D,hD,?_,?_⟩
  · apply hDb.trans
    rw [← pow_mul]
    apply pow_le_pow_right₀ hB
    nlinarith
  · intro m hm i k
    exact hDi (m+a i) (by have := ha i; omega) i k

/-- Fixed frame constants and fixed natural shifts can be absorbed together. -/
theorem finiteShiftedFrameCombination_prefix_denominators
    {ι κ : Type*} [Fintype ι] (c : ι →K) (f : ι →ℕ →κ →K) (a : ι →ℕ)
    (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ i k,IsIntegral ℤ ((D:K)*f i m k)) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ k,IsIntegral ℤ ((D:K)*(∑ i,c i*f i (m+a i) k)) := by
  obtain ⟨E,hE,hd⟩ := finiteFrameShift_prefix_denominators f a B hB hden
  exact finiteFrameCombination_prefix_denominators c (fun i m k =>f i (m+a i) k) E hE hd

end StrictEUnit
end
