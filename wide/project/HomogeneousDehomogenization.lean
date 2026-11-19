import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Actual homogeneous-component extraction and dehomogenization at t=1.
The strict degree bound is proved, not supplied as a finiteness premise. -/
noncomputable section
open MvPolynomial
namespace StrictEUnit
variable {k ι : Type*} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

def dehomogenize : MvPolynomial (Option ι) k →ₐ[k] MvPolynomial ι k :=
  MvPolynomial.aeval (fun o => Option.elim o 1 MvPolynomial.X)

@[simp] theorem dehomogenize_none : dehomogenize (k := k) (ι := ι) (X none) = 1 := by
  simp [dehomogenize]
@[simp] theorem dehomogenize_some (i : ι) : dehomogenize (k := k) (X (some i)) = X i := by
  simp [dehomogenize]

theorem homogeneousComponent_X_mul {σ : Type*} (i : σ) (n : ℕ)
    (p : MvPolynomial σ k) :
    homogeneousComponent (n+1) (X i * p) = X i * homogeneousComponent n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    have hd := isHomogeneous_monomial r (rfl : d.degree = d.degree)
    have hm := (isHomogeneous_X k i).mul hd
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hd]
    by_cases h : n = d.degree
    · simp [h, Nat.add_comm]
    · have h' : n+1 ≠ 1+d.degree := by omega
      simp [h, h']
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

theorem dehomogenize_totalDegree_le (p : MvPolynomial (Option ι) k) :
    (dehomogenize p).totalDegree ≤ p.totalDegree := by
  classical
  have hm (d : Option ι →₀ ℕ) (r : k) :
      (dehomogenize (monomial d r)).totalDegree ≤ d.degree := by
    simp only [dehomogenize, aeval_monomial]
    apply le_trans (totalDegree_mul _ _)
    simp only [algebraMap_eq, totalDegree_C, zero_add]
    apply le_trans (totalDegree_finset_prod _ _)
    apply Finset.sum_le_sum
    intro o ho
    apply le_trans (totalDegree_pow _ _)
    cases o <;> simp
  conv_lhs => rw [p.as_sum]
  simp only [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  exact (hm d _).trans (le_totalDegree hd)

theorem homogeneousIdeal_component_mem (I : Ideal (MvPolynomial (Option ι) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option ι) k))
    {p : MvPolynomial (Option ι) k} (hp : p ∈ I) (n : ℕ) :
    homogeneousComponent n p ∈ I := by
  have hh := hI n hp
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using hh

theorem dehomogenize_power_relation (I : Ideal (MvPolynomial (Option ι) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option ι) k))
    (i : ι) (N : ℕ) (hN : 0 < N)
    (h : X (some i) ^ N ∈ I ⊔ Ideal.span {X none}) :
    ∃ q : MvPolynomial ι k, q.totalDegree < N ∧
      X i ^ N - q ∈ Ideal.map (dehomogenize (k := k)).toRingHom I := by
  classical
  obtain ⟨f, hf, g, hg, he⟩ := Submodule.mem_sup.mp h
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hg
  let q := dehomogenize (homogeneousComponent (N-1) g)
  refine ⟨q, ?_, ?_⟩
  · exact lt_of_le_of_lt ((dehomogenize_totalDegree_le _).trans
      (homogeneousComponent_isHomogeneous _ _).totalDegree_le) (by omega)
  · have he' := congrArg (homogeneousComponent N) he
    have hpow := isHomogeneous_X_pow (R := k) (some i) N
    have hn : N = (N-1)+1 := by omega
    rw [map_add, homogeneousComponent_of_mem hpow] at he'
    simp only [ite_true] at he'
    have ht : homogeneousComponent N (X none * g) =
        X none * homogeneousComponent (N-1) g := by
      conv_lhs => rw [hn]
      exact homogeneousComponent_X_mul none (N-1) g
    rw [ht] at he'
    have hf' := homogeneousIdeal_component_mem I hI hf N
    have hfmap := Ideal.mem_map_of_mem dehomogenize.toRingHom hf'
    have eqf : X i ^ N - q = dehomogenize (homogeneousComponent N f) := by
      have hemap := congrArg dehomogenize he'
      simp only [map_add, map_mul, map_pow, dehomogenize_none, dehomogenize_some,
        one_mul] at hemap
      exact (sub_eq_iff_eq_add).mpr (by simpa only [q] using hemap.symm)
    rw [eqf]
    exact hfmap

end StrictEUnit
#print axioms StrictEUnit.dehomogenize
#print axioms StrictEUnit.dehomogenize_none
#print axioms StrictEUnit.dehomogenize_some
#print axioms StrictEUnit.homogeneousComponent_X_mul
#print axioms StrictEUnit.dehomogenize_totalDegree_le
#print axioms StrictEUnit.homogeneousIdeal_component_mem
#print axioms StrictEUnit.dehomogenize_power_relation
