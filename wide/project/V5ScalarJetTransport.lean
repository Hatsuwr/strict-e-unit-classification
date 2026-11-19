import V5FiniteJetKernel
import V5ScalarIndicialJet

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

private def v5IteratedOrdinaryLinear (K : Type*) [Field K] :
    ℕ → PowerSeries K →ₗ[K] PowerSeries K
  | 0 => LinearMap.id
  | n+1 => (PowerSeries.derivative K).toLinearMap.comp (v5IteratedOrdinaryLinear K n)

private theorem v5_iteratedOrdinaryLinear_apply (j : ℕ) (x : PowerSeries K) :
    v5IteratedOrdinaryLinear K j x = (PowerSeries.derivative K)^[j] x := by
  induction j with
  | zero => rfl
  | succ n ih => rw [v5IteratedOrdinaryLinear, LinearMap.comp_apply, Function.iterate_succ_apply', ← ih]; rfl

def v5ScalarODELinear (p : ℕ → Polynomial K) (N : ℕ) : PowerSeries K →ₗ[K] PowerSeries K :=
  ∑ i ∈ Finset.range N, (LinearMap.mulLeft K (p i : PowerSeries K)).comp (v5IteratedOrdinaryLinear K i)

theorem v5_scalarODELinear_apply (p : ℕ → Polynomial K) (N : ℕ) (x : PowerSeries K) :
    v5ScalarODELinear p N x = v5ScalarODE p N x := by
  simp only [v5ScalarODELinear, v5ScalarODE, LinearMap.coeFn_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, v5_iteratedOrdinaryLinear_apply]

/-- Coefficient of the scalar ODE on a basis monomial. Its finite slice is
the matrix of all early constraints, not a merely necessary truncation. -/
def v5ScalarJetEntry (p : ℕ → Polynomial K) (N e j : ℕ) : K :=
  PowerSeries.coeff K e (v5ScalarODE p N (PowerSeries.monomial K j 1))

theorem v5_scalar_jet_entry_eq
    (p : ℕ → Polynomial K) (N D h c : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hzero : ∀ j, h < j → stage26_odeSymbol p N D j = 0)
    (x : PowerSeries K) (e : Fin (c+D)) :
    PowerSeries.coeff K e.val (v5ScalarODE p N x) =
      ∑ j : Fin (c+h), v5ScalarJetEntry p N e.val j.val * PowerSeries.coeff K j.val x := by
  classical
  let trunc := ∑ j : Fin (c+h), PowerSeries.coeff K j.val x • PowerSeries.monomial K j.val 1
  have htrunc : ∀ j < c+h, PowerSeries.coeff K j x = PowerSeries.coeff K j trunc := by
    intro j hj
    symm
    simp only [trunc, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_monomial,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨j,hj⟩]
    · simp
    · intro i _ hi
      have hi' : j ≠ i.val := fun he => hi (Fin.ext he.symm)
      simp [hi']
    · simp
  rw [v5_scalar_early_depends_on_jet p N D h c hdeg hzero x trunc htrunc e.val e.isLt]
  simp only [trunc, ← v5_scalarODELinear_apply, map_sum, map_smul, PowerSeries.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => by rw [v5_scalarODELinear_apply, v5ScalarJetEntry, mul_comm])

theorem v5_scalarODE_map {L : Type*} [Field L]
    (φ : K →+* L) (p : ℕ → Polynomial K) (N : ℕ) (x : PowerSeries K) :
    PowerSeries.map φ (v5ScalarODE p N x) =
      v5ScalarODE (fun i => (p i).map φ) N (PowerSeries.map φ x) := by
  simp only [v5ScalarODE, map_sum, map_mul, ordinaryBorel_map_iterate_derivative,
    ← Polynomial.polynomial_map_coe]

theorem v5_scalar_jet_entry_map {L : Type*} [Field L]
    (φ : K →+* L) (p : ℕ → Polynomial K) (N e j : ℕ) :
    φ (v5ScalarJetEntry p N e j) = v5ScalarJetEntry (fun i => (p i).map φ) N e j := by
  unfold v5ScalarJetEntry
  rw [← PowerSeries.coeff_map, v5_scalarODE_map]
  have hm : PowerSeries.map φ (PowerSeries.monomial K j 1) = PowerSeries.monomial L j 1 := by
    ext k
    rw [PowerSeries.coeff_map, PowerSeries.coeff_monomial, PowerSeries.coeff_monomial]
    split_ifs <;> simp
  rw [hm]

/-- Convert the highest-shift recurrence into an exact triangular row. -/
private theorem v5_jet_tail_eq {K : Type*} [Field K] (Q : ℕ → Polynomial K)
    (h n : ℕ) (hh : h ≤ n) (u : ℕ → K) :
    (∑ j ∈ Finset.range (h+1), (Q j).eval ((n-h : ℕ) : K) * u (n-h+j) = 0) ↔
    (Q h).eval ((n-h : ℕ) : K) * u n =
      ∑ j : Fin n, (if n-h ≤ j.val then -(Q (j.val-(n-h))).eval ((n-h : ℕ) : K) else 0) *
        u j.val := by
  rw [Finset.sum_range_succ, Nat.sub_add_cancel hh]
  rw [Fin.sum_univ_eq_sum_range (fun j => (if n-h ≤ j then
    -(Q (j-(n-h))).eval ((n-h : ℕ) : K) else 0) * u j)]
  have hsum :
      (∑ j ∈ Finset.range n, (if n-h ≤ j then -(Q (j-(n-h))).eval ((n-h : ℕ) : K) else 0) *
        u j) =
      -(∑ j ∈ Finset.range h, (Q j).eval ((n-h : ℕ) : K) * u (n-h+j)) := by
    conv_lhs => rw [show Finset.range n = Finset.range ((n-h)+h) by rw [Nat.sub_add_cancel hh]]
    rw [Finset.sum_range_add, ← Finset.sum_neg_distrib]
    have h0 : (∑ j ∈ Finset.range (n-h),
        (if n-h ≤ j then -(Q (j-(n-h))).eval ((n-h : ℕ) : K) else 0) * u j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg (not_le_of_gt (Finset.mem_range.mp hj)), zero_mul]
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos (by omega), show n-h+j-(n-h) = j by omega, neg_mul]
  rw [hsum]
  constructor <;> intro he
  · linear_combination he
  · linear_combination he

/-- An actual finite kernel exactly captures the initial coefficients of all
formal solutions; the same kernel transports under algebraic embeddings. -/
private theorem v5_scalar_jet_solution_iff
    (p : ℕ → Polynomial K) (N D h c : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D) (hh : h < D+N)
    (hz : ∀ j, h < j → stage26_odeSymbol p N D j = 0)
    (x : PowerSeries K) :
    v5ScalarODE p N x = 0 ↔
    V5JetSolution
      (fun (e : Fin (c+D)) (j : Fin (c+h)) => v5ScalarJetEntry p N e.val j.val)
      (fun n => (stage26_odeSymbol p N D h).eval ((n-h : ℕ) : K))
      (fun n j => if n-h ≤ j then -(stage26_odeSymbol p N D (j-(n-h))).eval ((n-h : ℕ) : K) else 0)
      (fun n => PowerSeries.coeff K n x) := by
  rw [v5_scalar_ode_iff_early_and_tail p N D h c hdeg hh hz]
  constructor
  · rintro ⟨he,ht⟩
    constructor
    · intro e
      rw [← v5_scalar_jet_entry_eq p N D h c hdeg hz x e]
      exact he e.val e.isLt
    · intro n hn
      exact (v5_jet_tail_eq (stage26_odeSymbol p N D) h n (by omega) (fun j => PowerSeries.coeff K j x)).mp (ht (n-h) (by omega))
  · rintro ⟨he,ht⟩
    constructor
    · intro e he'
      rw [v5_scalar_jet_entry_eq p N D h c hdeg hz x ⟨e,he'⟩]
      exact he ⟨e,he'⟩
    · intro n hn
      have he := (v5_jet_tail_eq (stage26_odeSymbol p N D) h (n+h) (by omega) (fun j => PowerSeries.coeff K j x)).mpr
        (ht (n+h) (by omega))
      simpa only [Nat.add_sub_cancel] using he

/-- Vanishing of the constant term of *all* formal scalar solutions is
independent of the chosen coefficient embedding. This does not assert that
all such solutions vanish from any one distinguished solution vanishing. -/
theorem v5_scalar_formal_constant_zero_across_maps
    {K : Type*} {L₁ L₂ : Type u} [Field K] [CharZero K] [Field L₁] [Field L₂]
    (φ : K →+* L₁) (ψ : K →+* L₂) (p : ℕ → Polynomial K) (N D : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D) (hp : ∃ i < N, p i ≠ 0)
    (h : ∀ x : PowerSeries L₁, v5ScalarODE (fun i => (p i).map φ) N x = 0 →
      PowerSeries.coeff L₁ 0 x = 0)
    (y : PowerSeries L₂) (hy : v5ScalarODE (fun i => (p i).map ψ) N y = 0) :
    PowerSeries.coeff L₂ 0 y = 0 := by
  obtain ⟨k,c₀,hk,_,hzero,hdiag,_⟩ := v5_scalar_indicial_recurrence p N D hdeg hp
  let c := c₀+1
  let M := fun (e : Fin (c+D)) (j : Fin (c+k)) => v5ScalarJetEntry p N e.val j.val
  let d := fun n : ℕ => (stage26_odeSymbol p N D k).eval ((n-k : ℕ) : K)
  let A := fun n j : ℕ => if n-k ≤ j then
      -(stage26_odeSymbol p N D (j-(n-k))).eval ((n-k : ℕ) : K) else 0
  let i₀ : Fin (c+k) := ⟨0,by dsimp [c]; omega⟩
  have hdiag' (n : ℕ) (hn : c+k ≤ n) : d n ≠ 0 := by
    exact hdiag (n-k) (by dsimp [c] at hn; omega)
  have hiff {L : Type u} [Field L] (ρ : K →+* L) (x : PowerSeries L) :
      v5ScalarODE (fun i => (p i).map ρ) N x = 0 ↔
      V5JetSolution (fun i j => ρ (M i j)) (fun n => ρ (d n))
        (fun n j => ρ (A n j)) (fun n => PowerSeries.coeff L n x) := by
    have hzero' (j : ℕ) (hj : k < j) :
        stage26_odeSymbol (fun i => (p i).map ρ) N D j = 0 := by
      rw [← v5_scalar_symbol_map, hzero j hj, Polynomial.map_zero]
    have hterm (n j : ℕ) :
        (if n-k ≤ j then -(stage26_odeSymbol (fun i => (p i).map ρ) N D (j-(n-k))).eval
            ((n-k : ℕ) : L) else 0) = ρ (A n j) := by
      dsimp only [A]
      split_ifs <;> simp [← v5_scalar_symbol_map, Polynomial.eval_map, ← Polynomial.hom_eval₂]
    have hdmap (n : ℕ) :
        (stage26_odeSymbol (fun i => (p i).map ρ) N D k).eval ((n-k : ℕ) : L) =
          ρ (d n) := by
      rw [← v5_scalar_symbol_map, Polynomial.eval_natCast_map]
    simpa only [M, ← v5_scalar_jet_entry_map, hterm, hdmap] using
      v5_scalar_jet_solution_iff (fun i => (p i).map ρ) N D k c
        (fun i hi => Polynomial.natDegree_map_le.trans (hdeg i hi)) hk hzero' x
  refine v5_jet_solution_coordinate_across_maps φ ψ M d A hdiag' i₀ ?_
    (fun n => PowerSeries.coeff L₂ n y) ((hiff ψ y).mp hy)
  intro u hu
  have hu' : V5JetSolution (fun i j => φ (M i j)) (fun n => φ (d n))
      (fun n j => φ (A n j)) (fun j => PowerSeries.coeff L₁ j (PowerSeries.mk u)) := by
    simpa only [PowerSeries.coeff_mk] using hu
  have he := (hiff φ (PowerSeries.mk u)).mpr hu'
  simpa only [PowerSeries.coeff_mk] using h (PowerSeries.mk u) he

#print axioms v5_scalar_formal_constant_zero_across_maps
#print axioms v5_scalar_jet_entry_eq
#print axioms v5_scalar_jet_entry_map
end StrictEUnit
end
