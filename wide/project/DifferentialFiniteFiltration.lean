import MatrixCandidateSurjectivity
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! Bounded-degree finite differential submodules. Finite generation here
is not projectivity, and no flatness assertion follows in this module. -/
noncomputable section
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
 [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
variable (dB : Derivation k B B) (d : Derivation k R R)
variable (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))

include hb in
theorem differential_span_stable (s : Set R)
    (hs : ∀ x ∈ s, d x ∈ Submodule.span B s) :
    ∀ x ∈ Submodule.span B s, d x ∈ Submodule.span B s := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simpa using (Submodule.span B s).zero_mem
  | add x y hx hy ihx ihy => simpa using (Submodule.span B s).add_mem ihx ihy
  | smul b x hx ih =>
    rw [Algebra.smul_def, d.leibniz, hb]
    exact (Submodule.span B s).add_mem
      (by simpa [Algebra.smul_def] using (Submodule.span B s).smul_mem b ih)
      (by simpa [Algebra.smul_def, mul_comm] using (Submodule.span B s).smul_mem (dB b) hx)

theorem differential_mul_stable (M N : Submodule B R)
    (hm : ∀ x ∈ M, d x ∈ M) (hn : ∀ x ∈ N, d x ∈ N) :
    ∀ x ∈ M*N, d x ∈ M*N := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro x hx y hy
    rw [d.leibniz]
    exact (M*N).add_mem (Submodule.mul_mem_mul hx (hn y hy))
      (by simpa [mul_comm] using Submodule.mul_mem_mul (hm x hx) hy)
  · intro x y hx hy
    simpa using (M*N).add_mem hx hy

include hb in
theorem differential_pow_stable (M : Submodule B R)
    (hm : ∀ x ∈ M, d x ∈ M) (n : ℕ) : ∀ x ∈ M^n, d x ∈ M^n := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨b,rfl⟩ := Submodule.mem_one.mp (by simpa using hx)
    simpa [hb] using (Submodule.mem_one.mpr ⟨dB b,rfl⟩ : algebraMap B R (dB b) ∈ (1 : Submodule B R))
  | succ n ih => exact differential_mul_stable d (M^n) M ih hm

def differentialPiece (s : Set R) (n : ℕ) : Submodule B R :=
  (Submodule.span B (insert 1 s))^n

theorem differentialPiece_fg (s : Set R) (hs : s.Finite) (n : ℕ) :
    (differentialPiece (B := B) s n).FG :=
  (Submodule.fg_span (hs.insert 1)).pow n

theorem differentialPiece_mono (s : Set R) : Monotone (differentialPiece (B := B) s) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  change x ∈ (Submodule.span B (insert 1 s))^n * Submodule.span B (insert 1 s)
  simpa using Submodule.mul_mem_mul hx
    (Submodule.subset_span (Set.mem_insert 1 s) : (1:R) ∈ Submodule.span B (insert 1 s))

include hb in
theorem differentialPiece_stable (s : Set R)
    (hs : ∀ x ∈ s, d x ∈ Submodule.span B (insert 1 s)) (n : ℕ) :
    ∀ x ∈ differentialPiece (B := B) s n, d x ∈ differentialPiece (B := B) s n := by
  apply differential_pow_stable dB d hb
  apply differential_span_stable dB d hb
  intro x hx
  rcases hx with rfl | hx
  · simpa using (Submodule.span B (insert (1:R) s)).zero_mem
  · exact hs x hx

theorem mem_some_differentialPiece (s : Set R) (x : R) (hx : x ∈ Algebra.adjoin B s) :
    ∃ n, x ∈ differentialPiece (B := B) s n := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by simpa [differentialPiece] using Submodule.subset_span (Set.mem_insert_of_mem 1 hx)⟩
  | algebraMap b => exact ⟨0, by simpa [differentialPiece] using (Submodule.mem_one.mpr ⟨b,rfl⟩ : algebraMap B R b ∈ (1 : Submodule B R))⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨n,hn⟩ := ihx
    obtain ⟨m,hm⟩ := ihy
    exact ⟨max n m, (differentialPiece s _).add_mem
      (differentialPiece_mono s (le_max_left _ _) hn)
      (differentialPiece_mono s (le_max_right _ _) hm)⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨n,hn⟩ := ihx
    obtain ⟨m,hm⟩ := ihy
    refine ⟨n+m, ?_⟩
    simpa [differentialPiece, pow_add] using Submodule.mul_mem_mul hn hm

theorem finite_mem_some_differentialPiece (s t : Set R) (ht : t.Finite)
    (hgen : t ⊆ Algebra.adjoin B s) :
    ∃ n, t ⊆ differentialPiece (B := B) s n := by
  classical
  induction t, ht using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x t hnot ht ih =>
    obtain ⟨n,hn⟩ := mem_some_differentialPiece s x (hgen (Set.mem_insert _ _))
    obtain ⟨m,hm⟩ := ih (fun y hy => hgen (Set.mem_insert_of_mem _ hy))
    refine ⟨max n m, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact differentialPiece_mono s (le_max_left _ _) hn
    · exact differentialPiece_mono s (le_max_right _ _) (hm hy)

#print axioms differential_span_stable
#print axioms differential_mul_stable
#print axioms differential_pow_stable
#print axioms differentialPiece
#print axioms differentialPiece_fg
#print axioms differentialPiece_mono
#print axioms differentialPiece_stable
#print axioms mem_some_differentialPiece
#print axioms finite_mem_some_differentialPiece
end StrictEUnit
