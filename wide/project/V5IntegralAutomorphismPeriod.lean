import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
open Function
namespace StrictEUnit
variable {B A : Type*} [CommRing B] [CommRing A] [IsDomain A] [Algebra B A]

/-- An integral element has positive period under a base-fixing algebra
automorphism: its orbit is confined to the finite roots of a monic polynomial. -/
theorem v5_integral_automorphism_period (σ : A ≃ₐ[B] A) (x : A)
    (hx : IsIntegral B x) : ∃ n : ℕ, 0 < n ∧ (σ ^ n) x = x := by
  obtain ⟨p, hp, hpx⟩ := hx
  let S := p.rootSet A
  have hS : S.Finite := p.rootSet_finite A
  letI : Finite S := hS.to_subtype
  have hroot : ∀ y ∈ S, σ y ∈ S := by
    intro y hy
    rw [Polynomial.mem_rootSet'] at hy ⊢
    refine ⟨hy.1, ?_⟩
    rw [Polynomial.aeval_algHom_apply, hy.2, map_zero]
  let f : S → S := fun y => ⟨σ y, hroot y y.property⟩
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact σ.injective (congrArg Subtype.val hyz)
  have hxS : x ∈ S := by
    rw [Polynomial.mem_rootSet']
    exact ⟨(hp.map (algebraMap B A)).ne_zero, hpx⟩
  obtain ⟨n, hn, hperiod⟩ := (Function.mem_periodicPts).mp (hf.mem_periodicPts ⟨x, hxS⟩)
  have hsemi : Function.Semiconj (Subtype.val : S → A) f σ := fun y => rfl
  have hper := hperiod.map hsemi
  exact ⟨n, hn, by simpa only [AlgEquiv.coe_pow] using hper⟩

/-- Finitely many integral elements admit a common positive period. -/
theorem v5_integral_finset_common_period (σ : A ≃ₐ[B] A) (s : Finset A)
    (hs : ∀ x ∈ s, IsIntegral B x) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ s, (σ ^ n) x = x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by omega, by simp⟩
  | @insert x s hxs ih =>
    obtain ⟨m, hm, hmx⟩ := v5_integral_automorphism_period σ x (hs x (Finset.mem_insert_self x s))
    obtain ⟨n, hn, hns⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · have hp : Function.IsPeriodicPt σ m y := by simpa only [AlgEquiv.coe_pow] using hmx
      simpa only [AlgEquiv.coe_pow] using hp.mul_const n
    · have hp : Function.IsPeriodicPt σ n y := by simpa only [AlgEquiv.coe_pow] using hns y hy
      simpa only [AlgEquiv.coe_pow] using hp.const_mul m

/-- A common period of the finite generators fixes their entire generated
subalgebra; stability need not be supplied separately for this conclusion. -/
theorem v5_integral_adjoin_common_period (σ : A ≃ₐ[B] A) (s : Finset A)
    (hs : ∀ x ∈ s, IsIntegral B x) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ Algebra.adjoin B (s : Set A), (σ ^ n) x = x := by
  obtain ⟨n, hn, hfix⟩ := v5_integral_finset_common_period σ s hs
  refine ⟨n, hn, ?_⟩
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hfix x hx
  | algebraMap b => exact (σ ^ n).commutes b
  | add x y hx hy hxf hyf => rw [map_add, hxf, hyf]
  | mul x y hx hy hxf hyf => rw [map_mul, hxf, hyf]

/-- Finitely generated integral subalgebras are fixed pointwise by one
positive power of any ambient base-fixing automorphism. -/
theorem v5_integral_fg_subalgebra_common_period (σ : A ≃ₐ[B] A)
    (S : Subalgebra B A) (hfg : S.FG)
    (hint : ∀ x ∈ S, IsIntegral B x) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ S, (σ ^ n) x = x := by
  obtain ⟨s, hs⟩ := hfg
  have hgens : ∀ x ∈ s, IsIntegral B x := by
    intro x hx
    apply hint x
    rw [← hs]
    exact Algebra.subset_adjoin hx
  obtain ⟨n, hn, hfix⟩ := v5_integral_adjoin_common_period σ s hgens
  exact ⟨n, hn, by simpa only [hs] using hfix⟩

end StrictEUnit
#print axioms StrictEUnit.v5_integral_automorphism_period
#print axioms StrictEUnit.v5_integral_finset_common_period
#print axioms StrictEUnit.v5_integral_adjoin_common_period

#print axioms StrictEUnit.v5_integral_fg_subalgebra_common_period
