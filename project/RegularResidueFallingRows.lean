import RegularPolynomialConnectionFace
import ConstantCompanionObstruction

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Normalized regular residue of the SAME scalar companion boundary. -/
def regularCompanionResidue {K : Type*} [Field K] (n : ℕ) (τ : K)
    (β : Fin (n+1) → K) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  constantCompanion n 1 (fun j => β j/τ)+Matrix.diagonal (fun j => (j.val:K))

def regularResidueStep {K : Type*} [Field K] (n : ℕ) (τ : K)
    (β : Fin (n+1) → K) (m : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  constantCompanion n 1 (fun j => β j/τ)+Matrix.diagonal (fun j => (j.val:K)-(m:K))

theorem regularResidueStep_eq {K : Type*} [Field K] (n : ℕ) (τ : K)
    (β : Fin (n+1) → K) (m : ℕ) :
    regularResidueStep n τ β m=regularCompanionResidue n τ β-(m:K) • 1 := by
  classical
  ext i j
  simp only [regularResidueStep,regularCompanionResidue,Matrix.add_apply,Matrix.sub_apply,
    Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  split_ifs <;> ring

/-- Ordered falling product M(M-I)...(M-(m-1)I), with empty product I. -/
def matrixFallingProduct {K : Type*} [Field K] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) K) : ℕ → Matrix (Fin r) (Fin r) K
  | 0 => 1
  | m+1 => matrixFallingProduct M m*(M-(m:K) • 1)

def regularResidueBinomialRow {K : Type*} [Field K] (n : ℕ) (τ : K)
    (β : Fin (n+1) → K) (m : ℕ) : Fin (n+1) → K :=
  (m.factorial:K)⁻¹ • ((Pi.single 0 1) ᵥ* matrixFallingProduct (regularCompanionResidue n τ β) m)

/-- The exact SAME extracted polynomial row evolves by the residue minus mI,
not by the constant companion orbit of the strictly irregular argument. -/
theorem polynomialConnectionFaceRow_regular_residue_step
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (ht : 0<T.natTrailingDegree)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1)) (m : ℕ) :
    let τ := T.coeff T.natTrailingDegree
    let β := polynomialCompanionFace n 1 1 T U
    let u := polynomialConnectionFaceRow n 1 1 T U
    u (m+1)=τ • (u m ᵥ* regularResidueStep n τ β m) := by
  classical
  let τ := T.coeff T.natTrailingDegree
  let β := polynomialCompanionFace n 1 1 T U
  let u := polynomialConnectionFaceRow n 1 1 T U
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hrec := (polynomialConnectionFaceRow_regular_recurrence n c T U hclear ht hV).2 m
  have hc := constantCompanion_row_action n (1:K) (fun j => β j/τ) (u m)
  funext j
  simp only [regularResidueStep,Matrix.vecMul_add,Pi.add_apply,Matrix.vecMul_diagonal,
    Pi.smul_apply,smul_eq_mul]
  cases j using Fin.cases with
  | zero =>
    rw [hc.1]
    simp only [Fin.val_zero,Nat.cast_zero]
    change u (m+1) 0=τ*(u m (Fin.last n)*(β 0/τ)+u m 0*((0:K)-(m:K)))
    dsimp only [u,τ,β]
    rw [hrec.1]
    field_simp [Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT]
    ring
  | succ j =>
    rw [hc.2 j]
    change u (m+1) j.succ=τ*(u m j.castSucc*1+u m (Fin.last n)*(β j.succ/τ)+
      u m j.succ*((j.succ.val:K)-(m:K)))
    dsimp only [u,τ,β]
    rw [hrec.2 j]
    field_simp [Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT]
    ring

/-- Literal falling-product identification for the SAME numerator coefficients. -/
theorem polynomialConnectionFaceRow_eq_residue_falling_product
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (ht : 0<T.natTrailingDegree)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1)) :
    let τ := T.coeff T.natTrailingDegree
    let β := polynomialCompanionFace n 1 1 T U
    ∀ m,polynomialConnectionFaceRow n 1 1 T U m=
      τ^m • ((Pi.single 0 1) ᵥ* matrixFallingProduct (regularCompanionResidue n τ β) m) := by
  intro τ β m
  induction m with
  | zero =>
    simpa only [matrixFallingProduct,Matrix.vecMul_one,pow_zero,one_smul] using
      (polynomialConnectionFaceRow_regular_recurrence n c T U hclear ht hV).1
  | succ m ih =>
    rw [polynomialConnectionFaceRow_regular_residue_step n c T U hT hclear ht hV m,ih,
      Matrix.vecMul_smul,smul_smul,Matrix.vecMul_vecMul,regularResidueStep_eq]
    rw [matrixFallingProduct,pow_succ]
    congr 1
    ring

/-- Factorial divided residue rows are literal normalized extracted coefficients. -/
theorem regularResidueBinomialRow_eq_normalized_face
    {K : Type*} [Field K] [CharZero K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (ht : 0<T.natTrailingDegree)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1)) (m : ℕ) (j : Fin (n+1)) :
    let τ := T.coeff T.natTrailingDegree
    let β := polynomialCompanionFace n 1 1 T U
    regularResidueBinomialRow n τ β m j=
      polynomialConnectionFaceRow n 1 1 T U m j/((m.factorial:K)*τ^m) := by
  intro τ β
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hu := congrFun (polynomialConnectionFaceRow_eq_residue_falling_product
    n c T U hT hclear ht hV m) j
  rw [hu]
  simp only [regularResidueBinomialRow,Pi.smul_apply,smul_eq_mul]
  dsimp only [τ,β]
  field_simp [Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT,
    show (m.factorial:K) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
  ring

end StrictEUnit
end
