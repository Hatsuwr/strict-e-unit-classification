import FiniteDifferentialPresentation
import DeterminantalIdealStability
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Actual cokernel presentations and constant presentation rank over a
nontrivial differentially simple ring. This does not assert projectivity. -/
noncomputable section
namespace StrictEUnit
variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

theorem matrixMinorIdeal_zero {m n : Type*} (A : Matrix m n B) :
    matrixMinorIdeal 0 A = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := matrixMinor_mem 0 A (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa using h

theorem matrixMinorIdeal_eq_bot_of_row_bound {m n : Type*} [Fintype m]
    (A : Matrix m n B) (r : ℕ) (hr : Fintype.card m < r) :
    matrixMinorIdeal r A = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro x ⟨u,v,rfl⟩
  change (A.submatrix u v).det = 0
  have hu : ¬ Function.Injective u := by
    intro hu
    have h := Fintype.card_le_of_injective u hu
    simp only [Fintype.card_fin] at h
    exact (Nat.not_le_of_lt hr) h
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hu
  exact Matrix.det_zero_of_row_eq hne (by funext a; simp [Matrix.submatrix, hij])

theorem matrixMinorIdeal_eq_bot_of_col_bound {m n : Type*} [Fintype n]
    (A : Matrix m n B) (r : ℕ) (hr : Fintype.card n < r) :
    matrixMinorIdeal r A = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro x ⟨u,v,rfl⟩
  change (A.submatrix u v).det = 0
  have hv : ¬ Function.Injective v := by
    intro hv
    have h := Fintype.card_le_of_injective v hv
    simp only [Fintype.card_fin] at h
    exact (Nat.not_le_of_lt hr) h
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hv
  exact Matrix.det_zero_of_column_eq hne (by intro a; simp [Matrix.submatrix, hij])

theorem matrixMinorIdeal_rank [Nontrivial B] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n B)
    (hdich : ∀ r, matrixMinorIdeal r A = ⊥ ∨ matrixMinorIdeal r A = ⊤) :
    ∃ r ≤ min (Fintype.card m) (Fintype.card n),
      matrixMinorIdeal r A = ⊤ ∧ matrixMinorIdeal (r+1) A = ⊥ := by
  classical
  have hz : ∃ r, matrixMinorIdeal r A = ⊥ :=
    ⟨Fintype.card m+1, matrixMinorIdeal_eq_bot_of_row_bound A _ (Nat.lt_succ_self _)⟩
  let q := Nat.find hz
  have hq : matrixMinorIdeal q A = ⊥ := Nat.find_spec hz
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, matrixMinorIdeal_zero] at hq
    exact top_ne_bot hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hprev : matrixMinorIdeal (q-1) A ≠ ⊥ := Nat.find_min hz (Nat.sub_lt hqpos (by decide : 0 < 1))
  have htop := (hdich (q-1)).resolve_left hprev
  have hm : q ≤ Fintype.card m+1 := Nat.find_min' hz
    (matrixMinorIdeal_eq_bot_of_row_bound A _ (Nat.lt_succ_self _))
  have hn : q ≤ Fintype.card n+1 := Nat.find_min' hz
    (matrixMinorIdeal_eq_bot_of_col_bound A _ (Nat.lt_succ_self _))
  refine ⟨q-1, le_min (Nat.sub_le_iff_le_add.mpr hm) (Nat.sub_le_iff_le_add.mpr hn), htop, ?_⟩
  simpa only [Nat.sub_add_cancel hqpos] using hq

variable {M : Type*} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

def presentationCokernelEquiv {n m : ℕ} (v : Fin n → M) (A : Matrix (Fin n) (Fin m) B)
    (hv : Function.Surjective (Fintype.linearCombination B v))
    (hA : Submodule.span B (Set.range fun j : Fin m => fun i : Fin n => A i j) =
      LinearMap.ker (Fintype.linearCombination B v)) :
    ((Fin n → B) ⧸ Submodule.span B (Set.range fun j : Fin m => fun i : Fin n => A i j)) ≃ₗ[B] M :=
  (Submodule.quotEquivOfEq _ _ hA).trans
    ((Fintype.linearCombination B v).quotKerEquivOfSurjective hv)

theorem finite_differential_presentation_constant_rank
    [IsNoetherianRing B] [Nontrivial B] [Module.Finite B M]
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (hD : ∀ b x, D (b • x) = δ b • x + b • D x)
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤) :
    ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) B),
      Nonempty (((Fin n → B) ⧸ Submodule.span B
        (Set.range fun j : Fin m => fun i : Fin n => A i j)) ≃ₗ[B] M) ∧
      (∀ r, matrixMinorIdeal r A = ⊥ ∨ matrixMinorIdeal r A = ⊤) ∧
      ∃ r ≤ min n m, matrixMinorIdeal r A = ⊤ ∧ matrixMinorIdeal (r+1) A = ⊥ := by
  obtain ⟨n,m,v,A,P,Q,hv,hA,hP,hδA⟩ := finite_differential_presentation δ D hD
  have heq : ∀ i j, δ (A i j) = ((-P)*A) i j + (A*Q) i j := by
    intro i j
    rw [hδA]
    simp only [Matrix.neg_mul, Matrix.sub_apply, Matrix.neg_apply]
    exact sub_eq_neg_add _ _
  have hdich := fun r => matrixMinorIdeal_eq_bot_or_top δ hsimple r A (-P) Q heq
  refine ⟨n,m,A,⟨presentationCokernelEquiv v A hv hA⟩,hdich,?_⟩
  simpa only [Fintype.card_fin] using matrixMinorIdeal_rank A hdich

theorem finite_differential_matrix_cokernel_rank
    [IsNoetherianRing B] [Nontrivial B] [Module.Finite B M]
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (hD : ∀ b x, D (b • x) = δ b • x + b • D x)
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤) :
    ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) B),
      Nonempty (((Fin n → B) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[B] M) ∧
      (∀ r, matrixMinorIdeal r A = ⊥ ∨ matrixMinorIdeal r A = ⊤) ∧
      ∃ r ≤ min n m, matrixMinorIdeal r A = ⊤ ∧ matrixMinorIdeal (r+1) A = ⊥ := by
  obtain ⟨n,m,A,he,hd,hr⟩ := finite_differential_presentation_constant_rank δ D hD hsimple
  refine ⟨n,m,A,?_,hd,hr⟩
  rw [Matrix.range_mulVecLin A]
  exact he

#print axioms finite_differential_matrix_cokernel_rank
#print axioms matrixMinorIdeal_zero
#print axioms matrixMinorIdeal_eq_bot_of_row_bound
#print axioms matrixMinorIdeal_eq_bot_of_col_bound
#print axioms matrixMinorIdeal_rank
#print axioms presentationCokernelEquiv
#print axioms finite_differential_presentation_constant_rank
end StrictEUnit
