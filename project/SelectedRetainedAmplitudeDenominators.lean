import FiniteAmplitudeFactorialArithmetic

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem selectedFuchsSourceData_retained_amplitude_denominators
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (B : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI B)
    (q : Fin (n+2) →Polynomial AlgebraicComplex)
    (hq : q=ordinaryReflectionTuple (n+1) (fun i =>
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n)
        (T.map (algebraMap (𝓞 K) K))
        (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) i).map phi))
    (hf : Stage56FiniteFuchs (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q))
    (hc : (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q)
      (Fin.last (n+1)) (Fin.last (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q))≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols _ hf 0) ≃
      Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q))
    (rho : Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q) →AlgebraicComplex)
    (p : Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q) →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude _ hf (e.symm i)) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤C^(N+1) ∧
      ∀ i m,m≤N →∀ t,IsIntegral ℤ ((D:AlgebraicComplex)*(m.factorial:AlgebraicComplex)*
        ((p i).coeff t).coeff (m:ℤ)) := by
  classical
  obtain ⟨E,hE,psi,htower,rhoE,pE,hrE,hpE,hbranch⟩ :=
    selectedFuchsSourceData_retained_family_factorial_arithmetic G a phi n hr c T UI B hsource
      q hq hf hc e rho p hrho hp
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  have hpEa (i) : FactorialLogPrefixArithmetic (pE i) := by
    by_cases hni : ∀ z : ℤ,rhoE i≠(z:E)
    · exact (hbranch i).1 hni
    · push_neg at hni
      obtain ⟨z,hz⟩ := hni
      have hs := factorialLogPrefixArithmetic_integer_shift _ ((hbranch i).2 z hz) (-z)
      rw [frobeniusIntegerShift_add,neg_add_cancel] at hs
      simpa only [frobeniusIntegerShift,HahnSeries.single_zero_one,map_one,one_mul] using hs
  have hpa (i) : FactorialLogPrefixArithmetic (p i) := by
    rw [← hpE i]
    exact factorialLogPrefixArithmetic_map (algebraMap E AlgebraicComplex) (pE i) (hpEa i)
  exact finite_factorialLogPrefixArithmetic p hpa
end StrictEUnit
end
