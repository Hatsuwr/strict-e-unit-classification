import FiniteForcingJetSolutions
import MinimalDifferentialCompanion

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The literal unweighted derivative jet, with no change of center. -/
def sourceOrdinaryDerivativeJet (n : ℕ) (f : LaurentSeries K) : Fin (n+1) → LaurentSeries K :=
  fun j =>(stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[j.val] f

def sourceCompanionResidual (n : ℕ) (c : Fin (n+1) → LaurentSeries K)
    (t f : LaurentSeries K) : LaurentSeries K :=
  t*((stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[n+1] f-
    ∑ j,c j*sourceOrdinaryDerivativeJet n f j)

/-- The forced companion equations have the exact shift rows and last row. -/
theorem sourceCompanion_forced_rows (n : ℕ) (c y : Fin (n+1) → LaurentSeries K)
    (t P : LaurentSeries K) :
    (∀ i,stage14_laurentAlgebraDerivation (y i)=
      (∑ j,minimalDerivativeCompanion (n+1) c i j*y j)+
        (if i.val+1=n+1 then t⁻¹ else 0)*P) ↔
    (stage14_laurentAlgebraDerivation (y (Fin.last n))=(∑ j,c j*y j)+t⁻¹*P) ∧
      ∀ i : Fin n,stage14_laurentAlgebraDerivation (y i.castSucc)=y i.succ := by
  have hlast : ∀ j,minimalDerivativeCompanion (n+1) c (Fin.last n) j=c j := by
    intro j;simp [minimalDerivativeCompanion]
  have hshift : ∀ i : Fin n,(∑ j,minimalDerivativeCompanion (n+1) c i.castSucc j*y j)=y i.succ := by
    intro i
    rw [Finset.sum_eq_single i.succ]
    · simp [minimalDerivativeCompanion,show i.val+1<n+1 by omega]
    · intro j hj hne
      have hjv : j.val≠i.val+1 := fun heq =>hne (Fin.ext heq)
      simp [minimalDerivativeCompanion,show i.val+1<n+1 by omega,hjv]
    · intro h;exact (h (Finset.mem_univ _)).elim
  constructor
  · intro h
    constructor
    · simpa only [hlast,Fin.val_last,ite_true] using h (Fin.last n)
    · intro i
      simpa only [hshift,Fin.coe_castSucc,if_neg (show i.val+1≠n+1 by omega),zero_mul,add_zero] using h i.castSucc
  · rintro ⟨hl,hs⟩ i
    refine Fin.lastCases ?_ (fun i =>?_) i
    · simpa only [hlast,Fin.val_last,ite_true] using hl
    · simpa only [hshift,Fin.coe_castSucc,if_neg (show i.val+1≠n+1 by omega),zero_mul,add_zero] using hs i

/-- Every vector satisfying the genuine shift rows is its first coordinate's
ordinary derivative jet; this is the reverse direction, not a chosen ansatz. -/
theorem sourceCompanion_reconstruct_jet (n : ℕ) (y : Fin (n+1) → LaurentSeries K)
    (h : ∀ i : Fin n,stage14_laurentAlgebraDerivation (y i.castSucc)=y i.succ) :
    y=sourceOrdinaryDerivativeJet n (y 0) := by
  have hj : ∀ m (hm : m<n+1),y ⟨m,hm⟩=
      (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[m] (y 0) := by
    intro m
    induction m with
    | zero =>intro hm;rfl
    | succ m ih =>
      intro hm
      let i : Fin n := ⟨m,by omega⟩
      have hi := h i
      change stage14_laurentAlgebraDerivation (y ⟨m,by omega⟩)=y ⟨m+1,hm⟩ at hi
      rw [← hi,ih,Function.iterate_succ_apply']
  funext j
  exact hj j.val j.isLt

/-- A canonical jet solves the forced companion exactly when its scalar
residual is P; division uses only t != 0, not a unit-at-zero assumption. -/
theorem sourceCompanion_jet_solution_iff (n : ℕ) (c : Fin (n+1) → LaurentSeries K)
    (t f P : LaurentSeries K) (ht : t≠0) :
    (∀ i,stage14_laurentAlgebraDerivation (sourceOrdinaryDerivativeJet n f i)=
      (∑ j,minimalDerivativeCompanion (n+1) c i j*sourceOrdinaryDerivativeJet n f j)+
        (if i.val+1=n+1 then t⁻¹ else 0)*P) ↔
    sourceCompanionResidual n c t f=P := by
  rw [sourceCompanion_forced_rows]
  have hs : ∀ i : Fin n,stage14_laurentAlgebraDerivation (sourceOrdinaryDerivativeJet n f i.castSucc)=
      sourceOrdinaryDerivativeJet n f i.succ := by
    intro i
    simp only [sourceOrdinaryDerivativeJet,Fin.coe_castSucc,Fin.val_succ,Function.iterate_succ_apply']
  rw [and_iff_left hs]
  have hlast : stage14_laurentAlgebraDerivation (sourceOrdinaryDerivativeJet n f (Fin.last n))=
      (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[n+1] f := by
    simp only [sourceOrdinaryDerivativeJet,Fin.val_last,Function.iterate_succ_apply']
  rw [hlast]
  unfold sourceCompanionResidual
  constructor
  · intro h;rw [h,add_sub_cancel_left,← mul_assoc,mul_inv_cancel₀ ht,one_mul]
  · intro h
    have h' := congrArg (fun z =>t⁻¹*z) h
    dsimp only at h'
    rw [← mul_assoc,inv_mul_cancel₀ ht,one_mul] at h'
    exact (sub_eq_iff_eq_add.mp h').trans (add_comm _ _)

/-- Complete forced-companion solution description, including every vector. -/
theorem sourceCompanion_solution_iff_exists_jet (n : ℕ) (c y : Fin (n+1) → LaurentSeries K)
    (t P : LaurentSeries K) (ht : t≠0) :
    (∀ i,stage14_laurentAlgebraDerivation (y i)=
      (∑ j,minimalDerivativeCompanion (n+1) c i j*y j)+
        (if i.val+1=n+1 then t⁻¹ else 0)*P) ↔
    ∃ f,y=sourceOrdinaryDerivativeJet n f ∧ sourceCompanionResidual n c t f=P := by
  constructor
  · intro h
    have hy := sourceCompanion_reconstruct_jet n y ((sourceCompanion_forced_rows n c y t P).mp h).2
    refine ⟨y 0,hy,?_⟩
    apply (sourceCompanion_jet_solution_iff n c t (y 0) P ht).mp
    simpa only [← hy] using h
  · rintro ⟨f,rfl,hf⟩
    exact (sourceCompanion_jet_solution_iff n c t f P ht).mpr hf

end StrictEUnit
end
