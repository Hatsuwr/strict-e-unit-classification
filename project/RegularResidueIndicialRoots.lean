import RegularResidueFallingRows
import Mathlib.RingTheory.Polynomial.Pochhammer

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The explicit falling-basis indicial polynomial of the SAME regular
companion residue. Rationality of its roots is not assumed. -/
def regularResidueIndicial {K : Type*} [Field K] (n : ℕ) (τ : K)
    (β : Fin (n+1) → K) : Polynomial K :=
  descPochhammer K (n+1)-∑ j,Polynomial.C (β j/τ)*descPochhammer K j.val

theorem constantCompanion_column_action {K : Type*} [Field K] (n : ℕ)
    (t : K) (β v : Fin (n+1) → K) :
    (constantCompanion n t β *ᵥ v) (Fin.last n)=∑ j,β j*v j ∧
    ∀ i : Fin n,(constantCompanion n t β *ᵥ v) i.castSucc=t*v i.succ := by
  classical
  constructor
  · simp only [constantCompanion,Fin.lastCases_last,Matrix.mulVec,dotProduct]
  · intro i
    simp [constantCompanion,Matrix.mulVec,dotProduct,Pi.single_apply]

/-- Every actual root gives an explicit eigenvector, whose zero coordinate
is ONE. No spectral vector or representation premise is supplied. -/
theorem regularResidueIndicial_root_eigenvector
    {K : Type*} [Field K] (n : ℕ) (τ : K) (β : Fin (n+1) → K)
    (ξ : K) (hξ : (regularResidueIndicial n τ β).eval ξ=0) :
    let v : Fin (n+1) → K := fun j => (descPochhammer K j.val).eval ξ
    v 0=1 ∧ regularCompanionResidue n τ β *ᵥ v=ξ • v := by
  classical
  intro v
  have hsum : (∑ j,(β j/τ)*v j)=v (Fin.last n)*(ξ-(n:K)) := by
    have h := hξ
    simp only [regularResidueIndicial,Polynomial.eval_sub,Polynomial.eval_finset_sum,
      Polynomial.eval_mul,Polynomial.eval_C,descPochhammer_succ_eval] at h
    exact (sub_eq_zero.mp h).symm
  have hc := constantCompanion_column_action n (1:K) (fun j => β j/τ) v
  refine ⟨?_,?_⟩
  · simp only [v,Fin.val_zero,descPochhammer_zero,Polynomial.eval_one]
  · rw [regularCompanionResidue,Matrix.add_mulVec]
    funext i
    simp only [Pi.add_apply,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]
    cases i using Fin.lastCases with
    | last =>
      rw [hc.1,hsum]
      simp only [Fin.val_last]
      ring
    | cast i =>
      rw [hc.2 i,one_mul]
      change (descPochhammer K (i.val+1)).eval ξ+(i.val:K)*
          (descPochhammer K i.val).eval ξ=ξ*(descPochhammer K i.val).eval ξ
      rw [descPochhammer_succ_eval]
      ring

theorem matrixFallingProduct_mulVec_eigenvector
    {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (v : Fin r → K) (ξ : K) (hMv : M *ᵥ v=ξ • v) :
    ∀ m,matrixFallingProduct M m *ᵥ v=(descPochhammer K m).eval ξ • v := by
  classical
  intro m
  induction m with
  | zero => simp [matrixFallingProduct]
  | succ m ih =>
    have hstep : (M-(m:K) • 1) *ᵥ v=(ξ-(m:K)) • v := by
      rw [Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,hMv]
      exact (sub_smul _ _ _).symm
    rw [matrixFallingProduct,← Matrix.mulVec_mulVec,hstep,Matrix.mulVec_smul,ih,
      smul_smul,descPochhammer_succ_eval]
    congr 1
    ring

/-- Pairing the actual residue binomial row with the EXPLICIT indicial
root vector is the literal scalar binomial quantity. -/
theorem regularResidueBinomialRow_indicial_pairing
    {K : Type*} [Field K] (n : ℕ) (τ : K) (β : Fin (n+1) → K)
    (ξ : K) (hξ : (regularResidueIndicial n τ β).eval ξ=0) (m : ℕ) :
    regularResidueBinomialRow n τ β m ⬝ᵥ
        (fun j => (descPochhammer K j.val).eval ξ)=
      (descPochhammer K m).eval ξ/(m.factorial:K) := by
  classical
  let v : Fin (n+1) → K := fun j => (descPochhammer K j.val).eval ξ
  obtain ⟨h0,hv⟩ := regularResidueIndicial_root_eigenvector n τ β ξ hξ
  have hv0 : v 0=1 := h0
  have hp := matrixFallingProduct_mulVec_eigenvector (regularCompanionResidue n τ β) v ξ hv m
  rw [regularResidueBinomialRow,smul_dotProduct,← Matrix.dotProduct_mulVec,hp]
  simp only [single_dotProduct,Pi.smul_apply,smul_eq_mul,one_mul,hv0,mul_one]
  simpa only [div_eq_mul_inv] using
    (mul_comm ((m.factorial:K)⁻¹) ((descPochhammer K m).eval ξ))

end StrictEUnit
end
