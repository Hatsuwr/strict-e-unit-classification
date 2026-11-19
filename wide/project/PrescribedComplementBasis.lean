import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Logic.Equiv.Fin.Basic

/-! New reconstruction, not recovered historical source. A prescribed vector
outside an independent family is the first member of a complementary family. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

private def optionSumSwap (α β : Type*) :
    (Option α ⊕ β) ≃ (Option β ⊕ α) where
  toFun
    | Sum.inl none => Sum.inl none
    | Sum.inl (some a) => Sum.inr a
    | Sum.inr b => Sum.inl (some b)
  invFun
    | Sum.inl none => Sum.inl none
    | Sum.inl (some b) => Sum.inr b
    | Sum.inr a => Sum.inl (some a)
  left_inv := by
    rintro (x | y)
    · cases x <;> rfl
    · rfl
  right_inv := by
    rintro (x | y)
    · cases x <;> rfl
    · rfl

private theorem sumExtend_inl {ι K V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    {v : ι → V} (h : LinearIndependent K v) (i : ι) :
    Basis.sumExtend h (Sum.inl i) = v i := by
  classical
  simp [Basis.sumExtend, Basis.reindex_apply]
  rfl

universe u v

theorem exists_option_complement_basis {K : Type u} {V : Type v}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    {s : ℕ} {b : Fin s → V} {c : V}
    (hb : LinearIndependent K b)
    (hc : c ∉ Submodule.span K (Set.range b)) :
    ∃ (T : Type v) (B : Basis (Option T ⊕ Fin s) K V),
      B (Sum.inl none) = c ∧ ∀ i, B (Sum.inr i) = b i := by
  classical
  let seed : Option (Fin s) → V := fun o => Option.casesOn' o c b
  have hs : LinearIndependent K seed := hb.option hc
  let T := Basis.sumExtendIndex hs
  let B₀ : Basis (Option (Fin s) ⊕ T) K V := Basis.sumExtend hs
  refine ⟨T, B₀.reindex (optionSumSwap (Fin s) T), ?_, ?_⟩
  · rw [Basis.reindex_apply]
    change Basis.sumExtend hs (Sum.inl none) = c
    rw [sumExtend_inl]
    rfl
  · intro i
    rw [Basis.reindex_apply]
    change Basis.sumExtend hs (Sum.inl (some i)) = b i
    rw [sumExtend_inl]
    rfl

theorem exists_fin_complement_basis
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    {s : ℕ} {b : Fin s → V} {c : V}
    (hb : LinearIndependent K b)
    (hc : c ∉ Submodule.span K (Set.range b)) :
    ∃ (n : ℕ) (B : Basis (Fin (n + 1) ⊕ Fin s) K V),
      B (Sum.inl 0) = c ∧
      (∀ i, B (Sum.inr i) = b i) ∧
      n + 1 + s = Module.finrank K V := by
  classical
  obtain ⟨T, B₀, h₀, hb₀⟩ := exists_option_complement_basis hb hc
  letI : Fintype (Option T ⊕ Fin s) :=
    FiniteDimensional.fintypeBasisIndex B₀
  letI : Fintype T :=
    Fintype.ofInjective
      (fun t : T => (Sum.inl (some t) : Option T ⊕ Fin s))
      (by
        intro a b h
        exact Option.some.inj (Sum.inl.inj h))
  let e : Option T ≃ Fin (Fintype.card T + 1) :=
    (Equiv.optionCongr (Fintype.equivFin T)).trans
      (finSuccEquiv (Fintype.card T)).symm
  let B : Basis (Fin (Fintype.card T + 1) ⊕ Fin s) K V :=
    B₀.reindex (Equiv.sumCongr e (Equiv.refl (Fin s)))
  have he₀ : e.symm (0 : Fin (Fintype.card T + 1)) = none := by
    simp [e]
  refine ⟨Fintype.card T, B, ?_, ?_, ?_⟩
  · change
      B₀.reindex (Equiv.sumCongr e (Equiv.refl (Fin s)))
        (Sum.inl 0) = c
    rw [Basis.reindex_apply]
    change B₀ (Sum.inl (e.symm 0)) = c
    rw [he₀]
    exact h₀
  · intro i
    change
      B₀.reindex (Equiv.sumCongr e (Equiv.refl (Fin s)))
        (Sum.inr i) = b i
    rw [Basis.reindex_apply]
    change B₀ (Sum.inr i) = b i
    exact hb₀ i
  · simpa only [Fintype.card_sum, Fintype.card_fin] using
      (Module.finrank_eq_card_basis B).symm

theorem exists_prescribed_complement_family
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    {s : ℕ} {b : Fin s → V} {c : V}
    (hb : LinearIndependent K b)
    (hc : c ∉ Submodule.span K (Set.range b)) :
    ∃ (m : ℕ) (hm : 0 < m) (v : Fin m → V),
      v ⟨0, hm⟩ = c ∧
      LinearIndependent K (Sum.elim v b) ∧
      Submodule.span K (Set.range (Sum.elim v b)) = ⊤ ∧
      m + s = Module.finrank K V := by
  classical
  obtain ⟨n, B, h₀, hbB, hdim⟩ := exists_fin_complement_basis hb hc
  let v : Fin (n + 1) → V := fun i => B (Sum.inl i)
  have hfun :
      Sum.elim v b = (B : (Fin (n + 1) ⊕ Fin s) → V) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (hbB i).symm
  refine ⟨n + 1, Nat.zero_lt_succ n, v, ?_, ?_, ?_, hdim⟩
  · exact h₀
  · rw [hfun]
    exact B.linearIndependent
  · rw [hfun]
    exact B.span_eq

end StrictEUnit
