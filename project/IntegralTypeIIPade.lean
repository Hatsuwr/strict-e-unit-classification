import NumberFieldHousePade
import PadeMapPrefixTransport
import Mathlib.RingTheory.PowerSeries.Trunc

/-! SOURCE-ONLY: genuine Type-II simultaneous approximation. The finite matrix
has only common-denominator unknowns, not Type-I polynomial-row unknowns.
No rank theorem, balanced exponential corollary or denominator-growth claim. -/
noncomputable section
open scoped BigOperators Classical NumberField Matrix
namespace StrictEUnit

/-- Equations for coefficients N+1,...,N+M of each denominator product. -/
def typeIIPadeMatrix {R : Type*} (r N M : ℕ) (b : Fin r → ℕ → R) :
    Matrix (Fin r × Fin M) (Fin (N+1)) R :=
  fun jt k => b jt.1 (N+1+jt.2.val-k.val)

/-- Expose the original K-only Siegel constant before adjoining the zero case. -/
theorem exists_typeII_nonzero_kernel_constant (K : Type*) [Field K] [NumberField K] :
    ∃ κ : ℝ, ∀ (r N M : ℕ)
      (A : Matrix (Fin r × Fin M) (Fin (N+1)) (𝓞 K)) (H : ℝ),
      0 < r*M → r*M < N+1 → A ≠ 0 →
      (∀ i k, NumberField.house (A i k : K) ≤ H) →
      ∃ x : Fin (N+1) → 𝓞 K, x ≠ 0 ∧ A *ᵥ x = 0 ∧
        ∀ k, NumberField.house (x k : K) ≤
          κ * ((κ * (N+1) * H) ^
            (((r*M : ℕ) : ℝ) / ((N+1 : ℕ) - (r*M : ℕ) : ℝ))) := by
  classical
  refine ⟨?_, ?_⟩
  swap
  intro r N M A H hp hsize hA hH
  simpa only [Nat.cast_add, Nat.cast_one] using
    (NumberField.house.exists_ne_zero_int_vec_house_le
      (K := K) (a := A) (p := r*M) (q := N+1) (A := H)
      (h0p := hp) (hpq := hsize) (ha := hA) (habs := hH)
      (cardα := by simp) (cardβ := by simp))

/-- A public constant, with an explicit zero-matrix branch. In particular the
statement permits empty equation sets and arbitrarily late first coefficients. -/
theorem exists_typeII_small_kernel (K : Type*) [Field K] [NumberField K] :
    ∃ κ : ℝ, ∀ (r N M : ℕ)
      (A : Matrix (Fin r × Fin M) (Fin (N+1)) (𝓞 K)) (H : ℝ),
      r*M < N+1 → (∀ i k, NumberField.house (A i k : K) ≤ H) →
      ∃ x : Fin (N+1) → 𝓞 K, x ≠ 0 ∧ A *ᵥ x = 0 ∧
        ∀ k, NumberField.house (x k : K) ≤
          max 1 (κ * ((κ * (N+1) * H) ^
            (((r*M : ℕ) : ℝ) / ((N+1 : ℕ) - (r*M : ℕ) : ℝ)))) := by
  classical
  obtain ⟨κ, hκ⟩ := exists_typeII_nonzero_kernel_constant K
  refine ⟨κ, ?_⟩
  intro r N M A H hsize hH
  by_cases hA : A = 0
  · let x : Fin (N+1) → 𝓞 K := Pi.single 0 1
    refine ⟨x, ?_, ?_, ?_⟩
    · intro hx
      have he := congrFun hx 0
      exact (one_ne_zero : (1 : 𝓞 K) ≠ 0) (by simpa [x] using he)
    · simp [hA]
    · intro k
      by_cases hk : k = 0
      · subst k
        simpa [x, NumberField.house] using (le_max_left (1 : ℝ) _)
      · calc
          NumberField.house (x k : K) = 0 := by simp [x, hk, NumberField.house]
          _ ≤ 1 := zero_le_one
          _ ≤ _ := le_max_left _ _
  · have hp : 0 < r*M := by
      by_cases hr : r = 0
      · subst r
        exact False.elim (hA (by ext jt k; exact Fin.elim0 jt.1))
      by_cases hm : M = 0
      · subst M
        exact False.elim (hA (by ext jt k; exact Fin.elim0 jt.2))
      exact Nat.mul_pos (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hm)
    obtain ⟨x, hx, hker, hbound⟩ := hκ r N M A H hp hsize hA hH
    exact ⟨x, hx, hker, fun k => (hbound k).trans (le_max_right _ _)⟩

/-- Polynomial reconstruction only; this is not the Type-I matrix. -/
def typeIIPolynomial {R : Type*} [Semiring R] (N : ℕ) (x : Fin (N+1) → R) :
    Polynomial R := ∑ k, Polynomial.monomial k.val (x k)

theorem typeIIPolynomial_coeff {R : Type*} [Semiring R]
    (N : ℕ) (x : Fin (N+1) → R) (n : ℕ) :
    (typeIIPolynomial N x).coeff n = if h : n < N+1 then x ⟨n,h⟩ else 0 := by
  classical
  rw [typeIIPolynomial, Polynomial.finset_sum_coeff]
  by_cases hn : n < N+1
  · rw [dif_pos hn]
    rw [Finset.sum_eq_single (⟨n,hn⟩ : Fin (N+1))]
    · exact Polynomial.coeff_monomial_same _ _
    · intro k hk hne
      exact Polynomial.coeff_monomial_of_ne _ (fun he => hne (Fin.ext he))
    · simp
  · rw [dif_neg hn]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Polynomial.coeff_monomial, if_neg]
    intro he
    exact hn (he ▸ k.isLt)

theorem typeIIPolynomial_natDegree {R : Type*} [Semiring R]
    (N : ℕ) (x : Fin (N+1) → R) : (typeIIPolynomial N x).natDegree ≤ N := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ k.isLt)

/-- A finite convolution formula including the truncated low-index branches. -/
theorem typeIIPolynomial_mul_coeff {R : Type*} [CommSemiring R]
    (N : ℕ) (x : Fin (N+1) → R) (b : ℕ → R) (n : ℕ) :
    PowerSeries.coeff R n ((typeIIPolynomial N x : PowerSeries R) * PowerSeries.mk b) =
      ∑ k : Fin (N+1), if k.val ≤ n then x k * b (n-k.val) else 0 := by
  change PowerSeries.coeff R n
    (Polynomial.coeToPowerSeries.ringHom (∑ k, Polynomial.monomial k.val (x k)) *
      PowerSeries.mk b) = _
  rw [map_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change PowerSeries.coeff R n
    ((Polynomial.monomial k.val (x k) : PowerSeries R) * PowerSeries.mk b) = _
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hkn : k.val ≤ n
  · rw [if_pos hkn, PowerSeries.coeff_mk, if_pos hkn]
  · rw [if_neg hkn, if_neg hkn, mul_zero]

/-- Separate House calculation over the literal algebra map. -/
theorem typeII_C_mul_house (K : Type*) [Field K] [NumberField K]
    (δ : ℕ) (q : Polynomial (𝓞 K)) (D E : ℝ)
    (hD : (δ : ℝ) ≤ D) (hE : 0 ≤ E)
    (hq : ∀ n, NumberField.house (q.coeff n : K) ≤ E) :
    ∀ n, NumberField.house ((Polynomial.C (δ : 𝓞 K) * q).coeff n : K) ≤ D*E := by
  intro n
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  change NumberField.house (φ ((Polynomial.C (δ : 𝓞 K) * q).coeff n)) ≤ D*E
  rw [Polynomial.coeff_C_mul, map_mul, map_natCast]
  have hnat : NumberField.house (δ : K) = (δ : ℝ) := by
    simpa using (NumberField.house_intCast (K := K) (δ : ℤ))
  calc
    _ ≤ NumberField.house (δ : K) * NumberField.house (φ (q.coeff n)) :=
      NumberField.house_mul_le _ _
    _ ≤ (δ : ℝ) * E := by
      rw [hnat]
      exact mul_le_mul_of_nonneg_left (hq n) (Nat.cast_nonneg _)
    _ ≤ D*E := mul_le_mul_of_nonneg_right hD hE

/-- House bound for integral numerators before mapping to the original series. -/
theorem typeII_trunc_house (K : Type*) [Field K] [NumberField K]
    (N : ℕ) (x : Fin (N+1) → 𝓞 K) (b : ℕ → 𝓞 K) (H E : ℝ)
    (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hx : ∀ k, NumberField.house (x k : K) ≤ E)
    (hb : ∀ n, n ≤ N → NumberField.house (b n : K) ≤ H) :
    ∀ n, NumberField.house ((PowerSeries.trunc (N+1)
      ((typeIIPolynomial N x : PowerSeries (𝓞 K)) * PowerSeries.mk b)).coeff n : K)
        ≤ (N+1)*H*E := by
  intro n
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  change NumberField.house (φ ((PowerSeries.trunc (N+1)
    ((typeIIPolynomial N x : PowerSeries (𝓞 K)) * PowerSeries.mk b)).coeff n)) ≤ _
  rw [PowerSeries.coeff_trunc]
  by_cases hn : n < N+1
  · rw [if_pos hn, typeIIPolynomial_mul_coeff, map_sum]
    calc
      _ ≤ ∑ k : Fin (N+1), NumberField.house
          (φ (if k.val ≤ n then x k * b (n-k.val) else 0)) := by
        simpa using NumberField.house_sum_le_sum_house Finset.univ
          (fun k : Fin (N+1) => φ (if k.val ≤ n then x k*b (n-k.val) else 0))
      _ ≤ ∑ _k : Fin (N+1), E*H := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hkn : k.val ≤ n
        · rw [if_pos hkn, map_mul]
          exact (NumberField.house_mul_le _ _).trans
            (mul_le_mul (hx k) (hb _ (by omega))
              (NumberField.house_nonneg _) hE)
        · rw [if_neg hkn, map_zero]
          simpa [NumberField.house] using mul_nonneg hE hH
      _ = (N+1)*H*E := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]
        ring
  · rw [if_neg hn, map_zero]
    have hz : (0 : ℝ) ≤ (N+1)*H*E := mul_nonneg (mul_nonneg (by positivity) hH) hE
    simpa [NumberField.house] using hz

/-- Construction from a genuine underdetermined finite matrix, not from
supplied approximants. The SAME clearing scalar δ gives both the denominator
and integral numerators, and the literal truncation identity is retained. -/
theorem exists_integral_typeII_pade
    (K : Type*) [Field K] [NumberField K] :
    ∃ κ : ℝ, ∀ (r N M δ : ℕ) (f : Fin r → PowerSeries K)
      (b : Fin r → ℕ → 𝓞 K) (H D : ℝ),
      0 < δ → r*M < N+1 → 0 ≤ H → (δ : ℝ) ≤ D →
      (∀ j n, n ≤ N+M → (b j n : K) = (δ : K) * PowerSeries.coeff K n (f j)) →
      (∀ j n, n ≤ N+M → NumberField.house (b j n : K) ≤ H) →
      let E := max 1 (κ * ((κ * (N+1) * H) ^
        (((r*M : ℕ) : ℝ) / ((N+1 : ℕ) - (r*M : ℕ) : ℝ))))
      ∃ Q : Polynomial (𝓞 K), ∃ P : Fin r → Polynomial (𝓞 K),
        Q ≠ 0 ∧ Q.natDegree ≤ N ∧ (∀ j, (P j).natDegree ≤ N) ∧
        (∀ j, (P j).map (algebraMap (𝓞 K) K) = PowerSeries.trunc (N+1)
          ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K) * f j)) ∧
        (∀ j n, n < N+M+1 → PowerSeries.coeff K n
          (((Q.map (algebraMap (𝓞 K) K) : PowerSeries K) * f j) -
            ((P j).map (algebraMap (𝓞 K) K) : PowerSeries K)) = 0) ∧
        (∀ n, NumberField.house (Q.coeff n : K) ≤ D*E) ∧
        (∀ j n, NumberField.house ((P j).coeff n : K) ≤ (N+1)*H*E) := by
  obtain ⟨κ, hκ⟩ := exists_typeII_small_kernel K
  refine ⟨κ, ?_⟩
  intro r N M δ f b H D hδ hsize hH hD hb hhouse
  dsimp only
  let E := max 1 (κ * ((κ * (N+1) * H) ^
    (((r*M : ℕ) : ℝ) / ((N+1 : ℕ) - (r*M : ℕ) : ℝ))))
  have hE : 0 ≤ E := zero_le_one.trans (le_max_left _ _)
  obtain ⟨x, hx, hker, hbound⟩ := hκ r N M (typeIIPadeMatrix r N M b) H hsize
    (fun jt k => hhouse jt.1 _ (by have := jt.2.isLt; have := k.isLt; omega))
  let q0 := typeIIPolynomial N x
  let Q := Polynomial.C (δ : 𝓞 K) * q0
  let P : Fin r → Polynomial (𝓞 K) := fun j =>
    PowerSeries.trunc (N+1) ((q0 : PowerSeries (𝓞 K)) * PowerSeries.mk (b j))
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  have hq0 : q0 ≠ 0 := by
    intro hz
    apply hx
    funext k
    have he := congrArg (fun p : Polynomial (𝓞 K) => p.coeff k.val) hz
    simpa only [q0, typeIIPolynomial_coeff, dif_pos k.isLt, Polynomial.coeff_zero,
      Pi.zero_apply] using he
  have hQ : Q ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hδ))) hq0
  have hconv (j : Fin r) (n : ℕ) :
      PowerSeries.coeff (𝓞 K) n ((q0 : PowerSeries (𝓞 K)) * PowerSeries.mk (b j)) =
        ∑ k : Fin (N+1), if k.val ≤ n then x k * b j (n-k.val) else 0 :=
    typeIIPolynomial_mul_coeff N x (b j) n
  have hmap (j : Fin r) (n : ℕ) (hn : n ≤ N+M) :
      PowerSeries.coeff K n ((Q.map φ : PowerSeries K) * f j) =
        φ (PowerSeries.coeff (𝓞 K) n ((q0 : PowerSeries (𝓞 K)) * PowerSeries.mk (b j))) := by
    have hc := pade_coeff_mul_right_congr (q0.map φ : PowerSeries K)
      (PowerSeries.C K (δ : K) * f j) (PowerSeries.map φ (PowerSeries.mk (b j))) n
      (fun k hk => by rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
        PowerSeries.coeff_mk]; exact (hb j k (hk.trans hn)).symm)
    have hQmap : (Q.map φ : PowerSeries K) =
        PowerSeries.C K (δ : K) * (q0.map φ : PowerSeries K) := by
      change ((Polynomial.C (δ : 𝓞 K) * q0).map φ : PowerSeries K) = _
      rw [Polynomial.map_mul, Polynomial.map_C, map_natCast,
        Polynomial.coe_mul, Polynomial.coe_C]
    rw [hQmap, mul_assoc, mul_left_comm (PowerSeries.C K (δ : K)), hc]
    rw [← PowerSeries.coeff_map]
    congr 1
    rw [map_mul, Polynomial.polynomial_map_coe]
  have hzero (j : Fin r) (n : ℕ) (hlo : N < n) (hhi : n ≤ N+M) :
      PowerSeries.coeff (𝓞 K) n ((q0 : PowerSeries (𝓞 K)) * PowerSeries.mk (b j)) = 0 := by
    have ht : n-(N+1) < M := by omega
    have he := congrFun hker (j, ⟨n-(N+1),ht⟩)
    rw [hconv]
    change (∑ k : Fin (N+1), b j (N+1+(n-(N+1))-k.val) * x k) = 0 at he
    rw [show N+1+(n-(N+1)) = n by omega] at he
    calc
      _ = ∑ k : Fin (N+1), b j (n-k.val) * x k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos (show k.val ≤ n by have := k.isLt; omega), mul_comm]
      _ = 0 := he
  have hpmap (j : Fin r) : (P j).map φ =
      PowerSeries.trunc (N+1) ((Q.map φ : PowerSeries K) * f j) := by
    ext n
    rw [Polynomial.coeff_map]
    change φ ((PowerSeries.trunc (N+1)
      ((q0 : PowerSeries (𝓞 K)) * PowerSeries.mk (b j))).coeff n) = _
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    by_cases hn : n < N+1
    · rw [if_pos hn, if_pos hn, hmap j n (by omega)]
    · rw [if_neg hn, if_neg hn, map_zero]
  have hcoeffbound (n : ℕ) : NumberField.house (q0.coeff n : K) ≤ E := by
    rw [show q0 = typeIIPolynomial N x from rfl, typeIIPolynomial_coeff]
    split_ifs with hn
    · exact hbound ⟨n,hn⟩
    · simpa [NumberField.house] using hE
  refine ⟨Q, P, hQ, ?_, ?_, hpmap, ?_, ?_, ?_⟩
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (typeIIPolynomial_natDegree N x)
  · intro j
    exact Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt _ N)
  · intro j n hn
    rw [map_sub, Polynomial.coeff_coe, hpmap j, PowerSeries.coeff_trunc]
    by_cases hlo : n < N+1
    · rw [if_pos hlo, sub_self]
    · rw [if_neg hlo, sub_zero, hmap j n (by omega), hzero j n (by omega) (by omega), map_zero]
  · exact typeII_C_mul_house K δ q0 D E hD hE hcoeffbound
  · intro j
    exact typeII_trunc_house K N x (b j) H E hH hE hbound
      (fun n hn => hhouse j n (hn.trans (Nat.le_add_right N M)))

end StrictEUnit
end
