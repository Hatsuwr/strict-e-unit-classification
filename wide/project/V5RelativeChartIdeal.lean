import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w l t
variable {B : Type u} {R : Type v} {T : Type w} {J : Type l} {D : J → Type t}
  [CommRing B] [CommRing R] [CommRing T] [∀ j, CommRing (D j)]
  [Algebra B R] [Algebra B T] [∀ j, Algebra R (D j)] [DecidableEq J]

/-- In a split chart, the differences imposing tensor balance over the fixed
algebra generate exactly the kernel of the identity-component projection.
Here `E` represents the split base change of the fixed algebra, and
`i` is the distinguished component. -/
theorem v5_split_chart_balance_ideal (i : J)
    (l r : T →+* (∀ j, D j)) (E : R ⊗[B] T ≃ₐ[R] (J → R))
    (hr : ∀ x j, r x j = algebraMap R (D j) (E (1 ⊗ₜ[B] x) j))
    (hl : ∀ x j, l x j = algebraMap R (D j) (E (1 ⊗ₜ[B] x) i)) :
    Ideal.span (Set.range (fun x => r x - l x)) =
      RingHom.ker (Pi.evalRingHom D i) := by
  let I : Ideal (∀ j, D j) := Ideal.span (Set.range (fun x => r x - l x))
  change I = RingHom.ker (Pi.evalRingHom D i)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change r x i - l x i = 0
    rw [hr, hl, sub_self]
  · let d : (J → R) := fun j => if j = i then 0 else 1
    let e : ∀ j, D j := fun j => algebraMap R (D j) (d j)
    have hc (y : R ⊗[B] T) :
        (fun j => algebraMap R (D j) (E y j - E y i)) ∈ I := by
      induction y using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, Pi.zero_apply, sub_self]
        exact I.zero_mem
      | tmul a x =>
        have he : E (a ⊗ₜ[B] x) = a • E (1 ⊗ₜ[B] x) := by
          rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hprod :
            (fun j => algebraMap R (D j)
              (E (a ⊗ₜ[B] x) j - E (a ⊗ₜ[B] x) i)) =
              (fun j => algebraMap R (D j) a) * (r x - l x) := by
          funext j
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, map_mul, Pi.mul_apply,
            Pi.sub_apply, hr, hl, map_sub]
        rw [hprod]
        exact I.mul_mem_left _ (Ideal.subset_span ⟨x, rfl⟩)
      | add x y hx hy =>
        have hadd :
            (fun j => algebraMap R (D j) (E (x + y) j - E (x + y) i)) =
            (fun j => algebraMap R (D j) (E x j - E x i)) +
            (fun j => algebraMap R (D j) (E y j - E y i)) := by
          funext j
          simp only [map_add, Pi.add_apply]
          rw [add_sub_add_comm, map_add]
        rw [hadd]
        exact I.add_mem hx hy
    have he : e ∈ I := by
      have h := hc (E.symm d)
      simpa [e, d] using h
    intro x hx
    have hxi : x i = 0 := hx
    have hh : x * e = x := by
      funext j
      by_cases h : j = i
      · subst j
        simp [e, d, hxi]
      · simp [e, d, h]
    rw [← hh]
    exact I.mul_mem_left x he

section TensorBalance

variable [Algebra T R] [IsScalarTower B T R]

open Algebra.TensorProduct

/-- The ideal of the added balancing relations for changing the tensor base. -/
def v5_tensorBalanceIdeal : Ideal (R ⊗[B] R) :=
  Ideal.span (Set.range fun x : T =>
    1 ⊗ₜ[B] algebraMap T R x - algebraMap T R x ⊗ₜ[B] 1)

/-- Changing the base from `B` to `T` quotients out exactly the new
balancing relations, not merely an ideal containing them. -/
theorem v5_tensorBalance_kernel :
    RingHom.ker (mapOfCompatibleSMul' T B R R) =
      v5_tensorBalanceIdeal (B := B) (T := T) (R := R) := by
  let I : Ideal (R ⊗[B] R) := v5_tensorBalanceIdeal (B := B) (T := T) (R := R)
  let Q := (R ⊗[B] R) ⧸ I
  let p : R ⊗[B] R →+* Q := Ideal.Quotient.mk I
  let f : R →+* Q := p.comp includeLeftRingHom
  let g : R →+* Q := p.comp (includeRight : R →ₐ[B] R ⊗[B] R).toRingHom
  have hf (t : T) : g (algebraMap T R t) = f (algebraMap T R t) := by
    apply sub_eq_zero.mp
    change p (1 ⊗ₜ[B] algebraMap T R t) - p (algebraMap T R t ⊗ₜ[B] 1) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨t, rfl⟩)
  letI aRQ : Algebra R Q := f.toAlgebra
  letI aTQ : Algebra T Q := (f.comp (algebraMap T R)).toAlgebra
  letI : @IsScalarTower T R Q Algebra.toSMul aRQ.toSMul aTQ.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let gₐ : R →ₐ[T] Q :=
    { toRingHom := g
      commutes' := hf }
  let F : R ⊗[T] R →ₐ[R] Q :=
    lift (Algebra.ofId R Q) gₐ (fun a b => mul_comm _ _)
  let K := mapOfCompatibleSMul' T B R R
  have hk (a b : R) : K (a ⊗ₜ[B] b) = a ⊗ₜ[T] b := rfl
  change RingHom.ker K = I
  apply le_antisymm
  · have hfac (y : R ⊗[B] R) : F (K y) = p y := by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        rw [hk, lift_tmul]
        change p (a ⊗ₜ[B] 1) * p (1 ⊗ₜ[B] b) = p (a ⊗ₜ[B] b)
        rw [← map_mul, tmul_mul_tmul, mul_one, one_mul]
    intro y hy
    have hy' : K y = 0 := hy
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change p y = 0
    rw [← hfac, hy', map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change K (1 ⊗ₜ[B] algebraMap T R t - algebraMap T R t ⊗ₜ[B] 1) = 0
    rw [map_sub, hk, hk, tmul_one_eq_one_tmul, sub_self]
end TensorBalance

section RelativeChart
variable [Algebra T R] [IsScalarTower B T R]
open Algebra.TensorProduct

/-- Under the stated compatibility on the fixed algebra, the tensor product
over that algebra is the identity factor of the original split chart. -/
theorem v5_split_chart_identity_factor (i : J)
    (chart : R ⊗[B] R ≃ₐ[R] (∀ j, D j)) (E : R ⊗[B] T ≃ₐ[R] (J → R))
    (hr : ∀ t j, chart (1 ⊗ₜ[B] algebraMap T R t) j =
      algebraMap R (D j) (E (1 ⊗ₜ[B] t) j))
    (hl : ∀ t j, chart (algebraMap T R t ⊗ₜ[B] 1) j =
      algebraMap R (D j) (E (1 ⊗ₜ[B] t) i)) :
    ∃ rel : R ⊗[T] R ≃ₐ[R] D i, ∀ a b,
      rel (a ⊗ₜ[T] b) = chart (a ⊗ₜ[B] b) i := by
  let K := mapOfCompatibleSMul' T B R R
  let P := (Pi.evalRingHom D i).comp chart.toRingEquiv.toRingHom
  let l : T →+* (∀ j, D j) := chart.toRingEquiv.toRingHom.comp
    (includeLeftRingHom.comp (algebraMap T R))
  let r : T →+* (∀ j, D j) := chart.toRingEquiv.toRingHom.comp
    ((includeRight : R →ₐ[B] R ⊗[B] R).toRingHom.comp (algebraMap T R))
  have hspan := v5_split_chart_balance_ideal i l r E hr hl
  have hk : Function.Surjective K := mapOfCompatibleSMul_surjective T B R R
  have hp : Function.Surjective P := by
    intro x
    refine ⟨chart.symm (Function.update 0 i x), ?_⟩
    change chart (chart.symm (Function.update 0 i x)) i = x
    rw [chart.apply_symm_apply, Function.update_self]
  have hker : RingHom.ker K = RingHom.ker P := by
    rw [v5_tensorBalance_kernel]
    have hm :
        Ideal.map chart.toRingEquiv.toRingHom
           (v5_tensorBalanceIdeal (B := B) (T := T) (R := R)) =
             RingHom.ker (Pi.evalRingHom D i) := by
      unfold v5_tensorBalanceIdeal
      rw [Ideal.map_span, ← hspan]
      congr 1
      rw [← Set.range_comp]
      have heq : (⇑chart.toRingEquiv.toRingHom ∘ fun x : T =>
          1 ⊗ₜ[B] algebraMap T R x - algebraMap T R x ⊗ₜ[B] 1) =
          fun x => r x - l x := by
        funext t
        exact map_sub chart _ _
      rw [heq]
    ext x
    change x ∈ v5_tensorBalanceIdeal (B := B) (T := T) (R := R) ↔ P x = 0
    change _ ↔ chart x i = 0
    rw [← show chart x ∈ RingHom.ker (Pi.evalRingHom D i) ↔ chart x i = 0 from Iff.rfl,
      ← hm, Ideal.mem_map_iff_of_surjective chart.toRingEquiv.toRingHom chart.surjective]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := chart.injective hyx
      simpa [this] using hy
  let kEquiv := RingHom.quotientKerEquivOfSurjective hk
  let pEquiv := RingHom.quotientKerEquivOfSurjective hp
  let F := kEquiv.symm.trans ((Ideal.quotEquivOfEq hker).trans pEquiv)
  have hF (x : R ⊗[B] R) : F (K x) = P x := by
    have hkx : kEquiv (Ideal.Quotient.mk (RingHom.ker K) x) = K x := rfl
    rw [← hkx]
    change pEquiv (Ideal.quotEquivOfEq hker
      (kEquiv.symm (kEquiv (Ideal.Quotient.mk (RingHom.ker K) x)))) = _
    rw [kEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := F) (fun a => ?_), fun a b => hF (a ⊗ₜ[B] b)⟩
  change F (K (a ⊗ₜ[B] 1)) = algebraMap R (D i) a
  rw [hF]
  change chart (algebraMap R (R ⊗[B] R) a) i = _
  rw [chart.commutes]
  rfl
end RelativeChart
end StrictEUnit
#print axioms StrictEUnit.v5_split_chart_balance_ideal
#print axioms StrictEUnit.v5_tensorBalance_kernel
#print axioms StrictEUnit.v5_split_chart_identity_factor
