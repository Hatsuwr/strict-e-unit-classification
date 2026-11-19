import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-! NEW SOURCE-ONLY, UNCOMPILED. Finite polynomial approximation over a ring
of integers, using the existing public number-field Siegel theorem. The
existential constant is not asserted positive and no private symbol is named.
Nonzero matrix and entry-house bounds are explicit. No application to arbitrary
algebraic coefficients or global regularity is asserted. -/
noncomputable section
open scoped BigOperators Classical Matrix NumberField
namespace StrictEUnit
section Reconstruction
variable {R : Type*} [CommRing R] [Nontrivial R]

def finitePadeMatrix (r d s : ℕ) (a : Fin r → ℕ → R) :
    Matrix (Fin s) (Fin r × Fin (d+1)) R :=
  fun n jk => if jk.2.val ≤ n.val then a jk.1 (n.val-jk.2.val) else 0

def finitePadePolynomial (r d : ℕ) (t : Fin r × Fin (d+1) → R) (j : Fin r) :
    Polynomial R := ∑ k, Polynomial.monomial k.val (t (j,k))

theorem finitePadePolynomial_coeff (r d : ℕ) (t : Fin r × Fin (d+1) → R)
    (j : Fin r) (k : Fin (d+1)) :
    (finitePadePolynomial r d t j).coeff k.val = t (j,k) := by
  unfold finitePadePolynomial
  rw [Polynomial.finset_sum_coeff]
  calc
    _ = (Polynomial.monomial k.val (t (j,k)) : Polynomial R).coeff k.val := by
      apply Finset.sum_eq_single k
      · intro l hl hne
        rw [Polynomial.coeff_monomial, if_neg (fun h => hne (Fin.ext h))]
      · intro h
        exact (h (Finset.mem_univ k)).elim
    _ = _ := Polynomial.coeff_monomial_same _ _

theorem finitePadePolynomial_degree (r d : ℕ) (t : Fin r × Fin (d+1) → R)
    (j : Fin r) : (finitePadePolynomial r d t j).natDegree ≤ d := by
  unfold finitePadePolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun k : Fin (d+1) => Polynomial.monomial k.val (t (j,k))) ?_
  intro k hk
  exact le_trans (Polynomial.natDegree_monomial_le _) (Nat.le_of_lt_succ k.isLt)

theorem finitePadePolynomial_nonzero (r d : ℕ)
    (t : Fin r × Fin (d+1) → R) (ht : t ≠ 0) :
    ∃ j, finitePadePolynomial r d t j ≠ 0 := by
  by_contra h
  apply ht
  funext x
  have hp : finitePadePolynomial r d t x.1 = 0 := by
    by_contra hp
    exact h ⟨x.1, hp⟩
  have hc := congrArg (fun p : Polynomial R => p.coeff x.2.val) hp
  dsimp only at hc
  rw [finitePadePolynomial_coeff, Polynomial.coeff_zero] at hc
  exact hc

/-- The matrix equation is exactly the finite coefficient-vanishing system. -/
theorem finitePade_coefficient_matrix (r d s : ℕ) (a : Fin r → ℕ → R)
    (t : Fin r × Fin (d+1) → R) (n : Fin s) :
    PowerSeries.coeff R n.val
      (∑ j, (finitePadePolynomial r d t j : PowerSeries R) * PowerSeries.mk (a j)) =
        (finitePadeMatrix r d s a *ᵥ t) n := by
  have hmono (j : Fin r) (k : Fin (d+1)) :
      PowerSeries.coeff R n.val
        ((Polynomial.monomial k.val (t (j,k)) : Polynomial R) *
          PowerSeries.mk (a j) : PowerSeries R) =
        (if k.val ≤ n.val then a j (n.val-k.val) else 0) * t (j,k) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hk : k.val ≤ n.val
    · rw [if_pos hk, PowerSeries.coeff_mk, if_pos hk, mul_comm]
    · rw [if_neg hk, if_neg hk, mul_zero, zero_mul]
  have hrow (j : Fin r) :
      PowerSeries.coeff R n.val
        ((finitePadePolynomial r d t j : PowerSeries R) * PowerSeries.mk (a j)) =
        ∑ k : Fin (d+1), (if k.val ≤ n.val then a j (n.val-k.val) else 0) * t (j,k) := by
    change PowerSeries.coeff R n.val
      (Polynomial.coeToPowerSeries.ringHom
        (∑ k : Fin (d+1), Polynomial.monomial k.val (t (j,k))) * PowerSeries.mk (a j)) = _
    rw [map_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hmono j k
  rw [map_sum]
  simp only [hrow, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, finitePadeMatrix]

end Reconstruction

/-- Public existential interface hiding the implementation's private constant.
The witness is inferred from the bound in the public House theorem. -/
theorem exists_numberField_finitePade_kernel_constant
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ (r d s : ℕ) (a : Fin r → ℕ → 𝓞 K) (H : ℝ),
      0 < s → s < r*(d+1) → finitePadeMatrix r d s a ≠ 0 →
      (∀ n jk, NumberField.house ((finitePadeMatrix r d s a n jk : 𝓞 K) : K) ≤ H) →
      ∃ t : Fin r × Fin (d+1) → 𝓞 K,
        t ≠ 0 ∧ finitePadeMatrix r d s a *ᵥ t = 0 ∧
        ∀ jk, NumberField.house ((t jk : 𝓞 K) : K) ≤
          C * ((C * ((r*(d+1) : ℕ) : ℝ) * H) ^
            ((s : ℝ) / (((r*(d+1) : ℕ) : ℝ) - s))) := by
  classical
  refine ⟨?_, ?_⟩
  swap
  intro r d s a H hs hsize hA hH
  exact NumberField.house.exists_ne_zero_int_vec_house_le
    (K := K) (a := finitePadeMatrix r d s a) (p := s) (q := r*(d+1))
    (A := H) (h0p := hs) (hpq := hsize) (ha := hA) (habs := hH)
    (cardα := by simp only [Fintype.card_fin])
    (cardβ := by simp only [Fintype.card_prod, Fintype.card_fin])

/-- The same finite formal series and a genuinely nonzero polynomial vector.
The constant depends on K only; the matrix and H remain arbitrary. -/
theorem exists_bounded_numberField_pade
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ (r d s : ℕ) (a : Fin r → ℕ → 𝓞 K) (H : ℝ),
      0 < s → s < r*(d+1) → finitePadeMatrix r d s a ≠ 0 →
      (∀ n jk, NumberField.house ((finitePadeMatrix r d s a n jk : 𝓞 K) : K) ≤ H) →
      ∃ P : Fin r → Polynomial (𝓞 K),
        (∃ j, P j ≠ 0) ∧
        (∀ j, (P j).natDegree ≤ d) ∧
        (∀ j n, NumberField.house (((P j).coeff n : 𝓞 K) : K) ≤
          C * ((C * ((r*(d+1) : ℕ) : ℝ) * H) ^
            ((s : ℝ) / (((r*(d+1) : ℕ) : ℝ) - s)))) ∧
        (∀ n : ℕ, n < s → PowerSeries.coeff (𝓞 K) n
          (∑ j, (P j : PowerSeries (𝓞 K)) * PowerSeries.mk (a j)) = 0) := by
  classical
  obtain ⟨C, hC⟩ := exists_numberField_finitePade_kernel_constant K
  refine ⟨C, ?_⟩
  intro r d s a H hs hsize hA hH
  obtain ⟨t, ht, hkernel, hbound⟩ := hC r d s a H hs hsize hA hH
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    simp only [hr0, zero_mul] at hsize
    omega
  let j0 : Fin r := ⟨0, hr⟩
  let k0 : Fin (d+1) := ⟨0, Nat.succ_pos d⟩
  have hB : 0 ≤ C * ((C * ((r*(d+1) : ℕ) : ℝ) * H) ^
      ((s : ℝ) / (((r*(d+1) : ℕ) : ℝ) - s))) :=
    le_trans (NumberField.house_nonneg ((t (j0,k0) : 𝓞 K) : K)) (hbound (j0,k0))
  refine ⟨finitePadePolynomial r d t, finitePadePolynomial_nonzero r d t ht,
    finitePadePolynomial_degree r d t, ?_, ?_⟩
  · intro j n
    by_cases hn : n ≤ d
    · let k : Fin (d+1) := ⟨n, Nat.lt_succ_of_le hn⟩
      change NumberField.house (((finitePadePolynomial r d t j).coeff k.val : 𝓞 K) : K) ≤ _
      rw [finitePadePolynomial_coeff]
      exact hbound (j,k)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (finitePadePolynomial_degree r d t j) (by omega))]
      change NumberField.house (0 : K) ≤ _
      simpa only [NumberField.house, map_zero, norm_zero] using hB
  · intro n hn
    have h := congrArg (fun v : Fin s → 𝓞 K => v ⟨n, hn⟩) hkernel
    change (finitePadeMatrix r d s a *ᵥ t) ⟨n, hn⟩ = 0 at h
    rw [finitePade_coefficient_matrix r d s a t ⟨n, hn⟩]
    exact h

end StrictEUnit
end
