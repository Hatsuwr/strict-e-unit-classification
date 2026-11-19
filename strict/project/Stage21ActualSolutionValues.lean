import Stage21ArithmeticSolutionCoverage
import Stage21RealizedLogEvaluation

/-!
# Actual value coverage by algebraic connection coordinates

A formal relation among actual arithmetic entire solutions and the constructed
finite Laurent-log factor is lifted into a specifically realized algebra before
evaluation at (1,0). Thus no value is assigned to an arbitrary Laurent series.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual power pullback, represented in the genuine localized log algebra. -/
def stage21_ramifiedToRealizedLog (N : ℕ) (hN : N ≠ 0) :
    subfieldEntireFunctionAlgebra k →+* Polynomial (Stage21ActualLocalization k) :=
  (stage21_entireToRealizedLog k).comp (stage17_arithmeticPowerPullback k N hN).toRingHom

@[simp] theorem stage21_ramifiedToRealizedLog_formal (N : ℕ) (hN : N ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) :
    stage21_realizedLogFormal k (stage21_ramifiedToRealizedLog k N hN f) =
      stage17_ramifiedEntireFormalAlgHom k N hN f :=
  stage21_realizedLogFormal_entire k (stage17_arithmeticPowerPullback k N hN f)

@[simp] theorem stage21_ramifiedToRealizedLog_value (N : ℕ) (hN : N ≠ 0)
    (f : subfieldEntireFunctionAlgebra k) :
    stage21_realizedLogValueOne k (stage21_ramifiedToRealizedLog k N hN f) =
      stage14_subfieldEntireEvaluation k 1 f := by
  rw [stage21_ramifiedToRealizedLog, RingHom.comp_apply,
    stage21_realizedLogValueOne_entire]
  exact stage17_arithmeticPowerPullback_at_one k N hN f

/-- A formal connection identity is evaluated only after injectively lifting it
back to the realized polynomial-log algebra. -/
theorem stage21_formal_connection_realized
    (N : ℕ) (hN : N ≠ 0)
    (F V : Matrix n n (subfieldEntireFunctionAlgebra k))
    (Z : (Matrix n n (LaurentLogBase k))ˣ) (C : Matrix n n k)
    (hC : stage17_formalFrame k N hN V = stage17_formalFundamental k N hN F Z *
      C.map (algebraMap k (RatFunc (LaurentSeries k)))) :
    V.map (stage21_ramifiedToRealizedLog k N hN) =
      F.map (stage21_ramifiedToRealizedLog k N hN) *
      (Z : Matrix n n (LaurentLogBase k)).map (stage21_baseToRealizedLog k) *
      (C.map (algebraMap k (subfieldEntireFunctionAlgebra k))).map
        (stage21_ramifiedToRealizedLog k N hN) := by
  let τ := stage21_ramifiedToRealizedLog k N hN
  let β := stage21_baseToRealizedLog k
  let CE : Matrix n n (subfieldEntireFunctionAlgebra k) := C.map (algebraMap k (subfieldEntireFunctionAlgebra k))
  have hW (W : Matrix n n (subfieldEntireFunctionAlgebra k)) :
      (stage21_realizedLogFormal k).mapMatrix (W.map τ) = stage17_formalFrame k N hN W := by
    ext i j
    exact stage21_ramifiedToRealizedLog_formal k N hN (W i j)
  have hZ : (stage21_realizedLogFormal k).mapMatrix
      ((Z : Matrix n n (LaurentLogBase k)).map β) =
        (stage17_formalBaseMatrixUnit k Z : Matrix n n _) := by
    ext i j
    exact stage21_realizedLogFormal_base k (Z.val i j)
  have hCE : (stage21_realizedLogFormal k).mapMatrix (CE.map τ) =
      C.map (algebraMap k (RatFunc (LaurentSeries k))) := by
    rw [hW]
    ext i j
    exact (stage17_ramifiedEntireFormalAlgHom k N hN).commutes (C i j)
  have hR : V.map τ = F.map τ * (Z : Matrix n n (LaurentLogBase k)).map β * CE.map τ := by
    apply Matrix.map_injective (stage21_realizedLogFormal_injective k)
    change (stage21_realizedLogFormal k).mapMatrix (V.map τ) =
      (stage21_realizedLogFormal k).mapMatrix
        (F.map τ * (Z : Matrix n n (LaurentLogBase k)).map β * CE.map τ)
    rw [map_mul, map_mul, hW, hW, hZ, hCE]
    exact hC
  exact hR

/-- A formal connection identity is evaluated only after injectively lifting it
back to the realized polynomial-log algebra. -/
theorem stage21_formal_connection_implies_actual_value
    (N : ℕ) (hN : N ≠ 0)
    (F V : Matrix n n (subfieldEntireFunctionAlgebra k))
    (Z : (Matrix n n (LaurentLogBase k))ˣ) (C : Matrix n n k)
    (hp : (laurentLogBasePoint k).toRingHom.mapMatrix
      (Z : Matrix n n (LaurentLogBase k)) = 1)
    (hC : stage17_formalFrame k N hN V = stage17_formalFundamental k N hN F Z *
      C.map (algebraMap k (RatFunc (LaurentSeries k)))) :
    V.map (stage14_subfieldEntireEvaluation k 1) =
      F.map (stage14_subfieldEntireEvaluation k 1) * C.map k.subtype := by
  let τ := stage21_ramifiedToRealizedLog k N hN
  let β := stage21_baseToRealizedLog k
  let CE : Matrix n n (subfieldEntireFunctionAlgebra k) := C.map (algebraMap k (subfieldEntireFunctionAlgebra k))
  have hR := stage21_formal_connection_realized k N hN F V Z C hC
  have hWval (W : Matrix n n (subfieldEntireFunctionAlgebra k)) :
      (stage21_realizedLogValueOne k).mapMatrix (W.map τ) =
        W.map (stage14_subfieldEntireEvaluation k 1) := by
    ext i j
    exact stage21_ramifiedToRealizedLog_value k N hN (W i j)
  have hZval : (stage21_realizedLogValueOne k).mapMatrix
      ((Z : Matrix n n (LaurentLogBase k)).map β) = 1 := by
    have h : (stage21_realizedLogValueOne k).mapMatrix
        ((Z : Matrix n n (LaurentLogBase k)).map β) =
        k.subtype.mapMatrix ((laurentLogBasePoint k).toRingHom.mapMatrix
          (Z : Matrix n n (LaurentLogBase k))) := by
      ext i j
      exact stage21_realizedLogValueOne_base k (Z.val i j)
    rw [h, hp, map_one]
  have hCval : (stage21_realizedLogValueOne k).mapMatrix (CE.map τ) = C.map k.subtype := by
    rw [hWval]
    ext i j
    exact (stage14_subfieldEntireEvaluation k 1).commutes (C i j)
  have h := congrArg (stage21_realizedLogValueOne k).mapMatrix hR
  rw [map_mul, map_mul, hWval, hWval, hZval, hCval, mul_one] at h
  exact h

/-- Every actual arithmetic solution matrix has algebraic value coordinates in
the actual frame at one. Rational spectrum constructs all formal auxiliaries. -/
theorem stage21_actualSolutionMatrix_value_coverage [IsAlgClosed k]
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F V : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a)
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (hV : Stage17ActualEulerFrameRelation k B 0 V)
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ∃ C : Matrix n n k, V.map (stage14_subfieldEntireEvaluation k 1) =
      F.map (stage14_subfieldEntireEvaluation k 1) * C.map k.subtype := by
  obtain ⟨N, hN, Z, hp, C, hC⟩ :=
    stage21_actualFrame_exists_arithmetic_solution_coordinates k B M F V hrat hF hV h1
  exact ⟨C, stage21_formal_connection_implies_actual_value k N hN F V Z C hp hC⟩

end StrictEUnit
