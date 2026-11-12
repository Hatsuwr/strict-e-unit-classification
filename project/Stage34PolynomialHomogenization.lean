import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! A constructed, positive-degree homogenization over an arbitrary commutative
semiring. The extra variable is `none`; specializing it to one recovers the
original polynomial literally, including zero and empty variable types. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]

/-- Set the added variable to one and leave every original variable unchanged. -/
def stage34_dehom (R ι : Type*) [CommSemiring R] :
    MvPolynomial (Option ι) R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun o => o.elim 1 MvPolynomial.X)

@[simp]
theorem stage34_dehom_C (a : R) :
    stage34_dehom R ι (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [stage34_dehom]

@[simp]
theorem stage34_dehom_X_none :
    stage34_dehom R ι (MvPolynomial.X none) = 1 := by
  simp [stage34_dehom]

@[simp]
theorem stage34_dehom_X_some (i : ι) :
    stage34_dehom R ι (MvPolynomial.X (some i)) = MvPolynomial.X i := by
  simp [stage34_dehom]

/-- Sum the homogeneous components, padded to the positive degree deg(P)+1. -/
def stage34_hom (P : MvPolynomial ι R) : MvPolynomial (Option ι) R :=
  ∑ j ∈ Finset.range (P.totalDegree + 1),
    MvPolynomial.X none ^ (P.totalDegree + 1 - j) *
      MvPolynomial.rename some (MvPolynomial.homogeneousComponent j P)

theorem stage34_hom_degree_pos (P : MvPolynomial ι R) :
    0 < P.totalDegree + 1 := Nat.zero_lt_succ _

theorem stage34_hom_isHomogeneous (P : MvPolynomial ι R) :
    (stage34_hom P).IsHomogeneous (P.totalDegree + 1) := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  have hj' : j ≤ P.totalDegree + 1 := (Finset.mem_range.mp hj).le
  simpa only [Nat.sub_add_cancel hj'] using
    (MvPolynomial.isHomogeneous_X_pow (R := R) (none : Option ι)
      (P.totalDegree + 1 - j)).mul
      (MvPolynomial.homogeneousComponent_isHomogeneous j P).rename_isHomogeneous

@[simp]
theorem stage34_dehom_rename (P : MvPolynomial ι R) :
    stage34_dehom R ι (MvPolynomial.rename some P) = P := by
  simp [stage34_dehom, MvPolynomial.eval₂_rename, Function.comp_def]

/-- This is an equality of polynomials, not merely equality of their values. -/
@[simp]
theorem stage34_dehom_hom (P : MvPolynomial ι R) :
    stage34_dehom R ι (stage34_hom P) = P := by
  classical
  simp only [stage34_hom, map_sum, map_mul, map_pow, stage34_dehom_rename]
  rw [stage34_dehom_X_none]
  simpa only [one_pow, one_mul] using MvPolynomial.sum_homogeneousComponent P

/-- Evaluation commutes with setting the new coordinate equal to one. -/
theorem stage34_eval_dehom (κ : R →+* S) (v : ι → S)
    (Q : MvPolynomial (Option ι) R) :
    MvPolynomial.eval₂ κ v (stage34_dehom R ι Q) =
      MvPolynomial.eval₂ κ (fun o => o.elim 1 v) Q := by
  have h : (MvPolynomial.eval₂Hom κ v).comp (stage34_dehom R ι) =
      MvPolynomial.eval₂Hom κ (fun o => o.elim 1 v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [stage34_dehom]
    · intro o
      cases o <;> simp [stage34_dehom]
  exact DFunLike.congr_fun h Q

theorem stage34_eval_hom (κ : R →+* S) (v : ι → S)
    (P : MvPolynomial ι R) :
    MvPolynomial.eval₂ κ (fun o => o.elim 1 v) (stage34_hom P) =
      MvPolynomial.eval₂ κ v P := by
  rw [← stage34_eval_dehom, stage34_dehom_hom]

theorem stage34_hom_ne_zero {P : MvPolynomial ι R} (hP : P ≠ 0) :
    stage34_hom P ≠ 0 := by
  intro h
  apply hP
  have := congrArg (stage34_dehom R ι) h
  simpa only [stage34_dehom_hom, map_zero] using this

theorem stage34_hom_totalDegree {P : MvPolynomial ι R} (hP : P ≠ 0) :
    (stage34_hom P).totalDegree = P.totalDegree + 1 :=
  (stage34_hom_isHomogeneous P).totalDegree (stage34_hom_ne_zero hP)

@[simp]
theorem stage34_hom_zero : stage34_hom (0 : MvPolynomial ι R) = 0 := by
  simp [stage34_hom]

/-- Constants receive one copy of the new variable, including over empty types. -/
theorem stage34_hom_C (a : R) :
    stage34_hom (MvPolynomial.C a : MvPolynomial ι R) =
      MvPolynomial.X none * MvPolynomial.C a := by
  simp [stage34_hom]

end StrictEUnit
