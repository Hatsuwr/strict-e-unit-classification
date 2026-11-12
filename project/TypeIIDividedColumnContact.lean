import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination

/-! Source-only. Divided polynomial COLUMN recurrence; the matrix acts on the
left with a minus sign. This is not the connection-matrix W recurrence. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

def seriesContact (s : ℕ) (f : PowerSeries K) : Prop :=
  ∀ n, n < s → PowerSeries.coeff K n f = 0

theorem seriesContact_mono {s t : ℕ} {f : PowerSeries K}
    (h : seriesContact s f) (ht : t ≤ s) : seriesContact t f :=
  fun n hn => h n (lt_of_lt_of_le hn ht)

theorem seriesContact_sub {s : ℕ} {f g : PowerSeries K}
    (hf : seriesContact s f) (hg : seriesContact s g) : seriesContact s (f-g) := by
  intro n hn
  simp only [map_sub, hf n hn, hg n hn, sub_self]

theorem seriesContact_mul {s : ℕ} (f : PowerSeries K) {g : PowerSeries K}
    (hg : seriesContact s g) : seriesContact s (f*g) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
  rw [hg ab.2 (by omega), mul_zero]

theorem seriesContact_derivative {s : ℕ} {f : PowerSeries K}
    (hf : seriesContact s f) : seriesContact (s-1) (PowerSeries.derivative K f) := by
  intro n hn
  rw [PowerSeries.coeff_derivative, hf (n+1) (by omega), zero_mul]

theorem seriesContact_sum {ι : Type*} (I : Finset ι) (f : ι → PowerSeries K)
    (s : ℕ) (hf : ∀ i ∈ I, seriesContact s (f i)) :
    seriesContact s (∑ i ∈ I, f i) := by
  intro n hn
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi n hn)

/-- A field-polynomial construction, not an integrality assumption. -/
def typeIIDividedColumn (T : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (P : Fin r → Polynomial K) : ℕ → Fin r → Polynomial K
  | 0 => P
  | j+1 => fun i => Polynomial.C ((j+1 : K)⁻¹) *
      (T * (typeIIDividedColumn T U P j i).derivative -
        Polynomial.C (j : K) * T.derivative * typeIIDividedColumn T U P j i -
        ∑ l, U i l * typeIIDividedColumn T U P j l)

theorem typeIIDividedColumn_succ (T : Polynomial K)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K) (j : ℕ) (i : Fin r) :
    Polynomial.C (j+1 : K) * typeIIDividedColumn T U P (j+1) i =
      T * (typeIIDividedColumn T U P j i).derivative -
        Polynomial.C (j : K) * T.derivative * typeIIDividedColumn T U P j i -
        ∑ l, U i l * typeIIDividedColumn T U P j l := by
  have hj : (j+1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  simp only [typeIIDividedColumn, ← mul_assoc, ← Polynomial.C_mul,
    mul_inv_cancel₀ hj, Polynomial.C_1, one_mul]

theorem hasse_derivative_successor (Q : Polynomial K) (j : ℕ) :
    (Polynomial.hasseDeriv j Q).derivative =
      Polynomial.C (j+1 : K) * Polynomial.hasseDeriv (j+1) Q := by
  have h := congrArg (fun L : Polynomial K →ₗ[K] Polynomial K => L Q)
    (Polynomial.hasseDeriv_comp (R := K) 1 j)
  change Polynomial.hasseDeriv 1 (Polynomial.hasseDeriv j Q) =
    (1+j).choose 1 • (Polynomial.hasseDeriv (1+j) Q) at h
  simpa only [Polynomial.hasseDeriv_one, Nat.choose_one_right, Nat.add_comm 1 j,
    nsmul_eq_mul, map_add, map_one, Polynomial.C_eq_natCast, Nat.cast_add, Nat.cast_one] using h

/-- The scalar Hasse numerator obeys the matching cleared recurrence. -/
theorem typeII_scalar_hasse_step (T Q : Polynomial K) (j : ℕ) :
    Polynomial.C (j+1 : K) * (T^(j+1)*Polynomial.hasseDeriv (j+1) Q) =
      T*(T^j*Polynomial.hasseDeriv j Q).derivative -
        Polynomial.C (j : K)*T.derivative*(T^j*Polynomial.hasseDeriv j Q) := by
  rw [Polynomial.derivative_mul, hasse_derivative_successor]
  cases j with
  | zero => simp
  | succ j =>
      rw [Polynomial.derivative_pow]
      simp only [Nat.add_sub_cancel, Polynomial.C_eq_natCast, pow_succ]
      ring

/-- Literal Type-II error, formed from the SAME T,Q,f and constructed column. -/
def typeIIColumnError (T Q : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (P : Fin r → Polynomial K) (f : Fin r → PowerSeries K) (j : ℕ) (i : Fin r) :
    PowerSeries K :=
  ((T^j*Polynomial.hasseDeriv j Q : Polynomial K) : PowerSeries K)*f i -
    (typeIIDividedColumn T U P j i : PowerSeries K)

theorem typeIIColumnError_step (T Q : Polynomial K)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K)
    (f : Fin r → PowerSeries K)
    (hf : ∀ i, (T : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l) (j : ℕ) (i : Fin r) :
    PowerSeries.C K (j+1 : K)*typeIIColumnError T Q U P f (j+1) i =
      (T : PowerSeries K)*PowerSeries.derivative K (typeIIColumnError T Q U P f j i) -
      PowerSeries.C K (j : K)*(T.derivative : PowerSeries K)*typeIIColumnError T Q U P f j i -
      ∑ l, (U i l : PowerSeries K)*typeIIColumnError T Q U P f j l := by
  have hs := congrArg (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K)
    (typeII_scalar_hasse_step T Q j)
  have hr := congrArg (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K)
    (typeIIDividedColumn_succ T U P j i)
  simp only [map_mul, map_sub, map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C] at hs hr
  unfold typeIIColumnError
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_coe]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hcross :
      ((T^j*Polynomial.hasseDeriv j Q : Polynomial K) : PowerSeries K) *
        ((T : PowerSeries K)*PowerSeries.derivative K (f i)) =
      ∑ l, (U i l : PowerSeries K) *
        (((T^j*Polynomial.hasseDeriv j Q : Polynomial K) : PowerSeries K)*f l) := by
    rw [hf i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [Polynomial.coe_mul] at hs hr hcross ⊢
  linear_combination (f i)*hs - hr - hcross

/-- Contact loses at most one per column, even at a zero of T. -/
theorem typeIIColumnError_contact (T Q : Polynomial K)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K)
    (f : Fin r → PowerSeries K)
    (hf : ∀ i, (T : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (L : ℕ) (hcontact : ∀ i, seriesContact L ((Q : PowerSeries K)*f i-(P i : PowerSeries K))) :
    ∀ j i, seriesContact (L-j) (typeIIColumnError T Q U P f j i) := by
  intro j
  induction j with
  | zero => simpa [typeIIColumnError, typeIIDividedColumn, Polynomial.hasseDeriv_zero] using hcontact
  | succ j ih =>
      intro i n hn
      have hc : seriesContact (L-(j+1))
          (PowerSeries.C K (j+1 : K)*typeIIColumnError T Q U P f (j+1) i) := by
        rw [typeIIColumnError_step T Q U P f hf]
        apply seriesContact_sub
        · apply seriesContact_sub
          · apply seriesContact_mul
            exact seriesContact_mono (seriesContact_derivative (ih i)) (by omega)
          · exact seriesContact_mul _ (seriesContact_mono (ih i) (by omega))
        · exact seriesContact_sum Finset.univ _ _ (fun l _ =>
            seriesContact_mul _ (seriesContact_mono (ih l) (by omega)))
      have hz := hc n hn
      rw [PowerSeries.coeff_C_mul] at hz
      exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast Nat.succ_ne_zero j)

/-- Coarse degree growth of the actually constructed polynomial column. -/
theorem typeIIDividedColumn_degree (T : Polynomial K)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K) (N τ : ℕ)
    (hT : T.natDegree ≤ τ) (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N) :
    ∀ j i, (typeIIDividedColumn T U P j i).natDegree ≤ N+j*τ := by
  intro j
  induction j with
  | zero => simpa only [typeIIDividedColumn, Nat.zero_mul, Nat.add_zero] using hP
  | succ j ih =>
      intro i
      apply (Polynomial.natDegree_C_mul_le _ _).trans
      have hd (l : Fin r) : (typeIIDividedColumn T U P j l).derivative.natDegree ≤ N+j*τ :=
        (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (ih l))
      have hTd : T.derivative.natDegree ≤ τ :=
        (Polynomial.natDegree_derivative_le T).trans ((Nat.sub_le _ _).trans hT)
      have h₁ := Polynomial.natDegree_mul_le_of_le hT (hd i)
      have h₂ := Polynomial.natDegree_mul_le_of_le
        ((Polynomial.natDegree_C_mul_le (j : K) T.derivative).trans hTd) (ih i)
      have h₃ := Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
        (fun l => U i l * typeIIDividedColumn T U P j l)
        (fun l _ => Polynomial.natDegree_mul_le_of_le (hU i l) (ih l))
      have h := Polynomial.natDegree_sub_le_of_le
        (Polynomial.natDegree_sub_le_of_le h₁ h₂) h₃
      simpa only [max_self, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h

end StrictEUnit
end
