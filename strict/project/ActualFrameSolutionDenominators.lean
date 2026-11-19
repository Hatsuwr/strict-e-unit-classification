import ActualLogFrameSpanning
import FiniteFrameCombinationDenominators

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Actual spanning transfers frame arithmetic to every actual solution over
the same number field, including the integer Laurent shifts and log degrees.
The output uses a fixed shifted cutoff L, as does frame arithmetic itself. -/
theorem actualLogFrame_solution_prefix_denominators {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r →K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0)
    (A : ℤ) (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ m,m≤N →∀ s i t,IsIntegral ℤ ((D:K)*((Y i s).coeff t).coeff ((m:ℤ)+A)))
    (xi : K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j) :
    ∃ L : ℤ,∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ i t,IsIntegral ℤ ((D:K)*((u i).coeff ((m:ℤ)+L)).coeff t) := by
  classical
  obtain ⟨n,c,hclass,hs⟩ := actualLogFrame_spanning C rho Y hY hdet xi u hu
  let S : ℤ := ∑ j,|n j|
  have hn (j : Fin r) : n j≤S := (le_abs_self _).trans
    (Finset.single_le_sum (fun k hk =>abs_nonneg (n k)) (Finset.mem_univ j))
  let a : Fin r →ℕ := fun j =>(S-n j).toNat
  have ha (j : Fin r) : (a j:ℤ)=S-n j := Int.toNat_of_nonneg (sub_nonneg.mpr (hn j))
  let f : Fin r →ℕ →(Fin r × ℕ) →K := fun j m k =>((Y k.1 j).coeff k.2).coeff ((m:ℤ)+A)
  obtain ⟨E,hE,hd⟩ := finiteShiftedFrameCombination_prefix_denominators c f a B hB
    (by intro N; obtain ⟨D,hD,hDb,hDi⟩ := hden N; exact ⟨D,hD,hDb,fun m hm j k =>hDi m hm j k.1 k.2⟩)
  refine ⟨A+S,E,hE,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hd N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm i t
  have he : ((u i).coeff ((m:ℤ)+(A+S))).coeff t=∑ j,c j*f j (m+a j) (i,t) := by
    rw [hs i,HahnSeries.coeff_sum,Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
    have hi : (m:ℤ)+(A+S)=((m:ℤ)+(A+S)-n j)+n j := by ring
    rw [hi,HahnSeries.coeff_single_mul_add,Polynomial.coeff_C_mul]
    rw [logPolynomialToCoefficientSeries_double_coeff]
    dsimp only [f]
    rw [Nat.cast_add,ha j]
    congr 2 <;> ring
  rw [he]
  exact hDi m hm (i,t)

end StrictEUnit
end
