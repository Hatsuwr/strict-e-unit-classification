import FiniteFrameCombinationDenominators

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Finite polynomial jets have a common integral multiplier for ALL log
coefficients; the degree bound is constructed, not assumed. -/
theorem finitePolynomial_coeff_integral {ι : Type*} [Fintype ι]
    (p : ι →Polynomial K) : ∃ e : ℕ,0<e ∧ ∀ i t,IsIntegral ℤ ((e:K)*(p i).coeff t) := by
  classical
  let d := Finset.univ.sup (fun i =>(p i).natDegree)
  have hd (i : ι) : (p i).natDegree≤d := Finset.le_sup (f:=fun i =>(p i).natDegree) (Finset.mem_univ i)
  obtain ⟨e,he,hi⟩ := logJet_finite_family_integral (fun z : ι × Fin (d+1) =>(p z.1).coeff z.2.val)
  refine ⟨e,he,?_⟩
  intro i t
  by_cases ht : t<d+1
  · exact hi (i,⟨t,ht⟩)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hd i; omega),mul_zero]
    exact isIntegral_zero

/-- A fixed Laurent cutoff can be removed for nonnegative coefficients.
The finitely many missing polynomial coefficients are cleared explicitly. -/
theorem logPolynomial_tail_to_prefix {ι : Type*} [Fintype ι]
    (f : ι →ℤ →Polynomial K) (L : ℤ) (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ i t,IsIntegral ℤ ((D:K)*(f i ((m:ℤ)+L)).coeff t)) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ i t,IsIntegral ℤ ((D:K)*(f i (m:ℤ)).coeff t) := by
  classical
  obtain ⟨e,he,hei⟩ := finitePolynomial_coeff_integral
    (fun z : ι × Fin L.toNat =>f z.1 (z.2.val:ℤ))
  let A := (-L).toNat
  let B' := B^(A+1)
  have hB' : 1≤B' := one_le_pow₀ hB
  have he1 : (1:ℝ)≤e := by exact_mod_cast he
  refine ⟨(e:ℝ)*B',by nlinarith,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden (N+A)
  refine ⟨e*D,Nat.mul_pos he hD,?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    have hep : (e:ℝ)≤(e:ℝ)^(N+1) := by
      calc (e:ℝ)=(e:ℝ)^1 := by simp
           _ ≤ (e:ℝ)^(N+1) := pow_le_pow_right₀ he1 (by omega)
    have hb : (D:ℝ)≤B'^(N+1) := hDb.trans (by
      dsimp [B']; rw [← pow_mul]; apply pow_le_pow_right₀ hB; nlinarith)
    exact mul_le_mul hep hb (by positivity) (by positivity)
  · intro m hm i t
    by_cases hml : (m:ℤ)<L
    · have hmt : m<L.toNat := by omega
      have hi := hei (i,⟨m,hmt⟩) t
      have hd : IsIntegral ℤ (D:K) := by exact_mod_cast (isIntegral_algebraMap (R:=ℤ) (A:=K) (x:=(D:ℤ)))
      convert hd.mul hi using 1 <;> push_cast <;> ring
    · let j := ((m:ℤ)-L).toNat
      have hj : j≤N+A := by dsimp [j,A]; omega
      have heq : (j:ℤ)+L=(m:ℤ) := by dsimp [j]; omega
      have hi := hDi j hj i t
      rw [heq] at hi
      have hei' : IsIntegral ℤ (e:K) := by exact_mod_cast (isIntegral_algebraMap (R:=ℤ) (A:=K) (x:=(e:ℤ)))
      convert hei'.mul hi using 1 <;> push_cast <;> ring

end StrictEUnit
end
