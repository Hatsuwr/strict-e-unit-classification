import Stage23ArithmeticFrameNonvanishing

/-!
# Initial nonsingularity from genuine determinant nondegeneracy

An actual two-sided Laurent Euler frame need not be assumed nonsingular at one.
Its determinant may instead be nonzero as an actual entire function, as its
actual Taylor series, or as its genuine ramified formal Taylor determinant.
Laurent clearing and the proved homogeneous first-order uniqueness theorem
then supply nonsingularity at every nonzero point, including one.

This does not construct a normal-form basis or prove that a scalar solution
basis has nonzero Wronskian. The genuine determinant nondegeneracy is still an
input. No formal fundamental-matrix invertibility theorem is imported or used.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit
local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing
local instance (k : Subfield ℂ) : AddGroup (subfieldEntireFunctionAlgebra k) :=
  @AddCommGroup.toAddGroup _
    (@Ring.toAddCommGroup _ (subfieldEntireFunctionAlgebra k).toRing)

/-- Homogeneous first-order uniqueness for the actual determinant, with no
invertibility premise. The matrix relation may be given only off the origin. -/
theorem stage29_twoSided_det_eq_zero_of_zero_at_regular {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      (∑ l, (A i l).val z * (F l j).val z) -
        ∑ l, (F i l).val z * (C l j).val z)
    (c : ℂ) (hc : p.val c ≠ 0)
    (hzero : (F.map (entireEvaluation c)).det = 0) : F.det = 0 := by
  have hode := entireMatrix_determinant_two_sided_firstOrder p A C F
    (entireMatrix_two_sided_extend_across_origin p A C F hF)
  rw [← entireMatrix_evaluation_det] at hzero
  apply Subtype.ext
  exact entire_firstOrder_zero_of_regular p.property
    (A.trace.property.sub C.trace.property) F.det.property c hc hode hzero

variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- Construct an actual entire cleared system from the literal Laurent Euler
relation. This is independent of every determinant nondegeneracy assumption. -/
theorem stage29_arithmeticFrame_exists_cleared_system
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    ∃ L : ℕ, 1 ≤ L ∧ ∃ A C : Matrix n n entireFunctionAlgebra,
      ∀ z i j, (entireCoordinate^(L+1)).val z * deriv (F i j).val.val z =
        (∑ l, (A i l).val z * (F l j).val.val z) -
          ∑ l, (F i l).val.val z * (C l j).val z := by
  obtain ⟨L, hL, P, hP⟩ := stage16_laurentMatrix_exists_positive_clearing B
  let A : Matrix n n entireFunctionAlgebra :=
    fun i j => (Polynomial.aeval (subfieldEntireCoordinate k) (P i j)).val
  let C : Matrix n n entireFunctionAlgebra :=
    fun i j => (subfieldEntireCoordinate k ^ L *
      algebraMap k (subfieldEntireFunctionAlgebra k) (M i j)).val
  refine ⟨L, hL, A, C, ?_⟩
  intro z i j
  have h := congrArg (stage14_subfieldEntireEvaluation k z)
    (stage17_actualEulerFrame_cleared k B M F hF L P hP i j)
  rw [map_sub (stage14_subfieldEntireEvaluation k z)] at h
  simp only [map_mul, map_pow, map_sum, AlgHom.commutes] at h
  change z^L * (z * deriv (F i j).val.val z) =
    (∑ l, (Polynomial.aeval (subfieldEntireCoordinate k) (P i l)).val.val z *
      (F l j).val.val z) -
    ∑ l, z^L * (F i l).val.val z * (M l j : ℂ) at h
  change z^(L+1) * deriv (F i j).val.val z =
    (∑ l, (Polynomial.aeval (subfieldEntireCoordinate k) (P i l)).val.val z *
      (F l j).val.val z) -
    ∑ l, (F i l).val.val z * (z^L * (M l j : ℂ))
  rw [pow_succ, mul_assoc, h]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- A determinant zero at any nonzero complex point forces the entire
arithmetic determinant to be identically zero. No nonsingular point is assumed. -/
theorem stage29_arithmeticFrame_det_eq_zero_of_zero_at_regular
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (c : ℂ) (hc : c ≠ 0)
    (hzero : (F.map (stage14_subfieldEntireEvaluation k c)).det = 0) : F.det = 0 := by
  obtain ⟨L, _hL, A, C, hsystem⟩ :=
    stage29_arithmeticFrame_exists_cleared_system k B M F hF
  let G : Matrix n n entireFunctionAlgebra := F.map (subfieldEntireFunctionAlgebra k).val
  have hG : G.det = 0 :=
    stage29_twoSided_det_eq_zero_of_zero_at_regular (entireCoordinate^(L+1)) A C G
      (fun z _hz i j => hsystem z i j) c (pow_ne_zero _ hc) hzero
  apply Subtype.ext
  exact (RingHom.map_det (subfieldEntireFunctionAlgebra k).val.toRingHom F).trans hG

/-- Genuine nonzero determinant, rather than chosen-point invertibility,
propagates to every ordinary point of the actual Laurent Euler system. -/
theorem stage29_arithmeticFrame_det_nonzero_off_origin_of_det_ne_zero
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) (hne : F.det ≠ 0) :
    ∀ c : ℂ, c ≠ 0 → (F.map (stage14_subfieldEntireEvaluation k c)).det ≠ 0 := by
  intro c hc hzero
  exact hne (stage29_arithmeticFrame_det_eq_zero_of_zero_at_regular k B M F hF c hc hzero)

/-- The chosen initial nonsingularity is a consequence of actual determinant
nondegeneracy, not a new premise. -/
theorem stage29_arithmeticFrame_det_at_one_ne_zero_of_det_ne_zero
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) (hne : F.det ≠ 0) :
    (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 :=
  stage29_arithmeticFrame_det_nonzero_off_origin_of_det_ne_zero k B M F hF hne 1 one_ne_zero

/-- Under the actual equation, nonzero determinant as an entire-function-algebra
element is equivalent to nonsingularity at one. -/
theorem stage29_arithmeticFrame_det_ne_zero_iff_at_one
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    F.det ≠ 0 ↔ (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 := by
  refine ⟨stage29_arithmeticFrame_det_at_one_ne_zero_of_det_ne_zero k B M F hF, ?_⟩
  intro h1 hzero
  apply h1
  have hev : stage14_subfieldEntireEvaluation k 1 F.det =
      (F.map (stage14_subfieldEntireEvaluation k 1)).det :=
    RingHom.map_det (stage14_subfieldEntireEvaluation k 1).toRingHom F
  rw [← hev, hzero, map_zero]

/-- The actual determinant function is not identically zero exactly when the
arithmetic entire determinant element is nonzero. This needs no frame equation. -/
theorem stage29_actual_det_function_ne_zero_iff
    (F : Matrix n n (subfieldEntireFunctionAlgebra k)) :
    F.det.val.val ≠ (fun _ => 0) ↔ F.det ≠ 0 := by
  constructor
  · intro h hzero
    exact h (congrArg (fun f : subfieldEntireFunctionAlgebra k => f.val.val) hzero)
  · intro h hzero
    apply h
    apply Subtype.ext
    exact Subtype.ext hzero

/-- Taylor nondegeneracy concerns the full genuine Taylor determinant, not its
constant coefficient. Its equivalence to actual nondegeneracy uses injectivity. -/
theorem stage29_taylor_det_ne_zero_iff
    (F : Matrix n n (subfieldEntireFunctionAlgebra k)) :
    (F.map (subfieldEntireTaylorAlgHom k)).det ≠ 0 ↔ F.det ≠ 0 := by
  have ht : subfieldEntireTaylorAlgHom k F.det =
      (F.map (subfieldEntireTaylorAlgHom k)).det :=
    RingHom.map_det (subfieldEntireTaylorAlgHom k).toRingHom F
  rw [← ht]
  constructor
  · intro h hzero
    exact h (hzero ▸ map_zero (subfieldEntireTaylorAlgHom k))
  · intro h hzero
    exact h (subfieldEntireTaylorAlgHom_injective k
      (hzero.trans (map_zero (subfieldEntireTaylorAlgHom k)).symm))

/-- The desired initial determinant follows from genuine Taylor determinant
nondegeneracy and the actual relation, without assumed zero-freeness. -/
theorem stage29_arithmeticFrame_taylor_det_ne_zero_iff_at_one
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    (F.map (subfieldEntireTaylorAlgHom k)).det ≠ 0 ↔
      (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 :=
  (stage29_taylor_det_ne_zero_iff k F).trans
    (stage29_arithmeticFrame_det_ne_zero_iff_at_one k B M F hF)

/-- A nonzero genuine ramified formal determinant implies initial nonsingularity
through the actual determinant ODE. The opposite implication uses only actual
Taylor injectivity and the identity 1^N = 1, not a formal fundamental theorem. -/
theorem stage29_arithmeticFrame_formal_det_ne_zero_iff_at_one
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    (stage17_formalFrame k N hN F).det ≠ 0 ↔
      (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0 := by
  constructor
  · intro hformal
    apply stage29_arithmeticFrame_det_at_one_ne_zero_of_det_ne_zero k B M F hF
    intro hzero
    apply hformal
    have ht : stage17_ramifiedEntireFormalAlgHom k N hN F.det =
        (stage17_formalFrame k N hN F).det :=
      RingHom.map_det (stage17_ramifiedEntireFormalAlgHom k N hN).toRingHom F
    rw [← ht, hzero, map_zero]
  · intro h1 hzero
    have hmap : stage17_entireFormalAlgHom k
        (stage17_arithmeticPowerPullback k N hN F.det) = 0 :=
      (RingHom.map_det (stage17_ramifiedEntireFormalAlgHom k N hN).toRingHom F).trans hzero
    have hpullback := stage17_entireFormalAlgHom_injective k
      (hmap.trans (map_zero (stage17_entireFormalAlgHom k)).symm)
    have hvalue := congrArg (stage14_subfieldEntireEvaluation k 1) hpullback
    apply h1
    have hev : stage14_subfieldEntireEvaluation k 1 F.det =
        (F.map (stage14_subfieldEntireEvaluation k 1)).det :=
      RingHom.map_det (stage14_subfieldEntireEvaluation k 1).toRingHom F
    rw [← hev]
    change F.det.val.val 1 = 0
    change (stage17_arithmeticPowerPullback k N hN F.det).val.val 1 = 0 at hvalue
    simpa only [stage17_arithmeticPowerPullback_at_one] using hvalue

/-- Equivalent full nondegeneracy criteria for an actual arithmetic frame.
Zeros at the singular origin are allowed by every criterion. -/
theorem stage29_arithmeticFrame_nondegeneracy_criteria
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F) :
    (F.det.val.val ≠ (fun _ => 0) ↔
      (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) ∧
    ((F.map (subfieldEntireTaylorAlgHom k)).det ≠ 0 ↔
      (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) ∧
    ((stage17_formalFrame k N hN F).det ≠ 0 ↔
      (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) := by
  exact ⟨(stage29_actual_det_function_ne_zero_iff k F).trans
    (stage29_arithmeticFrame_det_ne_zero_iff_at_one k B M F hF),
    stage29_arithmeticFrame_taylor_det_ne_zero_iff_at_one k B M F hF,
    stage29_arithmeticFrame_formal_det_ne_zero_iff_at_one k N hN B M F hF⟩

end StrictEUnit
