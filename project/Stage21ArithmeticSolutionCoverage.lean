import Stage17ConstructedFormalFundamental

/-!
# Arithmetic solution coordinates in the constructed formal fundamental matrix

Both systems below are actual punctured analytic identities. The formal
fundamental matrix and its inverse are constructed from the arithmetic frame.
Their transition coordinates have derivative zero, so the already proved
no-extra-constants theorem places every coordinate in the original coefficient
field. No connection matrix or algebraic-constant hypothesis is supplied.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- The genuine ramified fundamental matrix as a chosen matrix unit, using its
proved invertibility rather than supplying an inverse. -/
def stage21_formalFundamentalUnit (N : ℕ) (hN : N ≠ 0)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0)
    (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    (Matrix n n (RatFunc (LaurentSeries k)))ˣ :=
  (stage17_formalFundamental_isUnit k N hN F h1 Z).unit

@[simp] theorem stage21_formalFundamentalUnit_val (N : ℕ) (hN : N ≠ 0)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0)
    (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    (stage21_formalFundamentalUnit k N hN F h1 Z : Matrix n n _) =
      stage17_formalFundamental k N hN F Z :=
  (stage17_formalFundamental_isUnit k N hN F h1 Z).unit_spec

/-- Any actual arithmetic entire solution matrix of zV′=BV has formal
coordinates over k in the constructed fundamental matrix. -/
theorem stage21_actualSolutionMatrix_has_arithmetic_coordinates
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F V : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (hV : Stage17ActualEulerFrameRelation k B 0 V)
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0)
    (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative (manuscriptBaseDerivation (k := k) N)
      (Z : Matrix n n (LaurentLogBase k)) =
        ramifiedConstantMatrix M * (Z : Matrix n n (LaurentLogBase k))) :
    ∃ C : Matrix n n k,
      stage17_formalFrame k N hN V = stage17_formalFundamental k N hN F Z *
        C.map (algebraMap k (RatFunc (LaurentSeries k))) := by
  let Y := stage21_formalFundamentalUnit k N hN F h1 Z
  let A := (B.map (stage17_laurentBasePullback k N)).map formalBaseEmbedding
  have hY : matrixDerivative (formalAmbientDerivation N hN) (Y : Matrix n n _) =
      A * (Y : Matrix n n _) := by
    rw [show (Y : Matrix n n _) = stage17_formalFundamental k N hN F Z from
      stage21_formalFundamentalUnit_val k N hN F h1 Z]
    exact stage17_formalFundamental_ode k N hN B M F hF Z hZ
  have hV' : matrixDerivative (formalAmbientDerivation N hN)
      (stage17_formalFrame k N hN V) = A * stage17_formalFrame k N hN V := by
    have h := stage17_formalFrame_ode k N hN B 0 V hV
    have hzero : (0 : Matrix n n k).map
        (algebraMap k (RatFunc (LaurentSeries k))) = 0 := by
      ext i j
      exact map_zero (algebraMap k (RatFunc (LaurentSeries k)))
    rw [hzero, mul_zero, sub_zero] at h
    exact h
  let T := (↑Y⁻¹ : Matrix n n (RatFunc (LaurentSeries k))) * stage17_formalFrame k N hN V
  have hc : matrixDerivative (formalAmbientDerivation N hN) T = 0 :=
    fundamental_matrix_transition_constant (formalAmbientDerivation N hN) A Y
      (stage17_formalFrame k N hN V) hY hV'
  have hentries (i j : n) : ∃ c : k,
      algebraMap k (RatFunc (LaurentSeries k)) c = T i j := by
    apply (formalAmbientDerivation_constants N hN (T i j)).mp
    exact congrArg (fun Q : Matrix n n (RatFunc (LaurentSeries k)) => Q i j) hc
  choose C hC using hentries
  have heq : Matrix.map C (algebraMap k (RatFunc (LaurentSeries k))) = T := by
    ext i j
    exact hC i j
  refine ⟨C, ?_⟩
  rw [heq, ← stage21_formalFundamentalUnit_val k N hN F h1 Z]
  change stage17_formalFrame k N hN V = (Y : Matrix n n _) *
    ((↑Y⁻¹ : Matrix n n _) * stage17_formalFrame k N hN V)
  rw [← mul_assoc, Units.mul_inv, one_mul]

/-- With rational spectrum, no supplied Jordan factor or algebraic connection
matrix is needed even for the formal coordinates. -/
theorem stage21_actualFrame_exists_arithmetic_solution_coordinates [IsAlgClosed k]
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F V : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a)
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (hV : Stage17ActualEulerFrameRelation k B 0 V)
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ∃ N : ℕ, ∃ hN : N ≠ 0, ∃ Z : (Matrix n n (LaurentLogBase k))ˣ,
      (laurentLogBasePoint k).toRingHom.mapMatrix (Z : Matrix n n (LaurentLogBase k)) = 1 ∧
      ∃ C : Matrix n n k,
        stage17_formalFrame k N hN V = stage17_formalFundamental k N hN F Z *
          C.map (algebraMap k (RatFunc (LaurentSeries k))) := by
  obtain ⟨N, hN, Z, hZ, hp, _, _⟩ :=
    stage17_actualFrame_exists_formalFundamental k B M F hrat hF h1
  obtain ⟨C, hC⟩ := stage21_actualSolutionMatrix_has_arithmetic_coordinates
    k N hN B M F V hF hV h1 Z hZ
  exact ⟨N, hN, Z, hp, C, hC⟩

end StrictEUnit
