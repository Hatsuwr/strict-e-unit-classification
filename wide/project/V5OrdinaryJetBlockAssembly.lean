import V5ActualOrdinaryJetBlock
import Mathlib.Data.Matrix.Block

noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {S : Type*} [Fintype S] [DecidableEq S] {m : S → ℕ}

private def v5_jetBlockFiberEquiv (s : S) :
    Fin (m s) ≃ {i : Σ t, Fin (m t) // i.1 = s} where
  toFun j := ⟨⟨s,j⟩,rfl⟩
  invFun i := cast (congrArg (fun t => Fin (m t)) i.property) i.val.2
  left_inv j := rfl
  right_inv := by
    rintro ⟨⟨t,j⟩,ht⟩
    dsimp at ht
    subst t
    rfl

/-- Assemble variable-size ordinary systems into a single block-diagonal
system, retaining each exact distinguished factor and only per-block
independence. The polynomial clearing is simultaneous at the same mark. -/
theorem v5_actual_ordinary_jet_blocks_assemble
    (k : Subfield ℂ) (α : k)
    (f : S → subfieldEntireFunctionAlgebra k)
    (g : ∀ s, Fin (m s) → subfieldEntireFunctionAlgebra k)
    (a : ∀ s, Fin (m s)) (hkeep : ∀ s, g s (a s) = f s)
    (B : ∀ s, Matrix (Fin (m s)) (Fin (m s)) (RatFunc k))
    (T : S → Polynomial k) (U : ∀ s, Matrix (Fin (m s)) (Fin (m s)) (Polynomial k))
    (hT : ∀ s, (T s).eval α ≠ 0)
    (hU : ∀ s i j, algebraMap (Polynomial k) (RatFunc k) (U s i j) =
      algebraMap (Polynomial k) (RatFunc k) (T s) * B s i j)
    (hlin : ∀ s, LinearIndependent (RatFunc k)
      (fun j => v5ActualEntireLaurentAlgHom k (g s j)))
    (hsys : ∀ s i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (g s i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (B s i j) *
        v5ActualEntireLaurentAlgHom k (g s j)) :
    let I := Σ s, Fin (m s)
    let G : I → subfieldEntireFunctionAlgebra k := fun i => g i.1 i.2
    let A := Matrix.blockDiagonal' B
    (∀ s, G ⟨s,a s⟩ = f s) ∧
    (∏ s, v5ActualEntireLaurentAlgHom k (G ⟨s,a s⟩)) =
      (∏ s, v5ActualEntireLaurentAlgHom k (f s)) ∧
    (∀ s, LinearIndependent (RatFunc k)
      (fun i : {i : I // i.1 = s} => v5ActualEntireLaurentAlgHom k (G i.val))) ∧
    (∀ i j, i.1 ≠ j.1 → A i j = 0) ∧
    (∀ i, laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k (G i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        v5ActualEntireLaurentAlgHom k (G j)) ∧
    ∃ t : Polynomial k, t.eval α ≠ 0 ∧
      ∃ V : Matrix I I (Polynomial k),
        ∀ i j, algebraMap (Polynomial k) (RatFunc k) (V i j) =
          algebraMap (Polynomial k) (RatFunc k) t * A i j := by
  refine ⟨hkeep, by simp only [hkeep], ?_, ?_, ?_, ?_⟩
  · intro s
    apply (linearIndependent_equiv (v5_jetBlockFiberEquiv (m := m) s)).mp
    exact hlin s
  · rintro ⟨s,i⟩ ⟨t,j⟩ hst
    exact Matrix.blockDiagonal'_apply_ne B i j hst
  · rintro ⟨s,i⟩
    change _ = ∑ j : Σ t, Fin (m t), _
    rw [Fintype.sum_sigma, Finset.sum_eq_single s]
    · simpa only [Matrix.blockDiagonal'_apply_eq] using hsys s i
    · intro t ht hts
      simp only [Matrix.blockDiagonal'_apply_ne B i _ (Ne.symm hts),
        map_zero, zero_mul, Finset.sum_const_zero]
    · simp
  · let t := ∏ s, T s
    let D : S → Polynomial k := fun s => ∏ r ∈ Finset.univ.erase s, T r
    have ht : t.eval α ≠ 0 := by
      dsimp [t]
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun s _ => hT s)
    have hD (s : S) : D s * T s = t :=
      Finset.prod_erase_mul Finset.univ T (Finset.mem_univ s)
    let W : ∀ s, Matrix (Fin (m s)) (Fin (m s)) (Polynomial k) := fun s i j => D s * U s i j
    refine ⟨t,ht,Matrix.blockDiagonal' W,?_⟩
    rintro ⟨s,i⟩ ⟨r,j⟩
    by_cases h : s = r
    · subst r
      simp only [Matrix.blockDiagonal'_apply_eq]
      change algebraMap (Polynomial k) (RatFunc k) (D s * U s i j) = _
      rw [map_mul, hU, ← mul_assoc, ← map_mul, hD]
    · rw [Matrix.blockDiagonal'_apply_ne B i j h, Matrix.blockDiagonal'_apply_ne W i j h,
        map_zero, mul_zero]

#print axioms v5_actual_ordinary_jet_blocks_assemble
end StrictEUnit
