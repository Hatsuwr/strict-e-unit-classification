import StrictEFunctionDefinitions
import Stage15RationalRamifiedFundamental

/-! The intended coefficient field really is algebraically closed. This uses
the actual relative algebraic closure of ℚ inside ℂ and its proved absolute
algebraic-closure property, rather than an extra matrix-theorem assumption. -/
noncomputable section
namespace StrictEUnit

/-- The actual algebraic numbers inside ℂ form an algebraically closed field. -/
theorem algebraicComplex_isAlgClosed : IsAlgClosed AlgebraicComplex :=
  IsAlgClosure.isAlgClosed ℚ

/-- Specialization of the constructed ramified fundamental unit to the exact
algebraic-number field used in the strict E-function definition. Only the
actual matrix and its rational-spectrum condition remain inputs. -/
theorem algebraicComplex_rational_matrix_fundamental_unit
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n AlgebraicComplex)
    (hrat : ∀ a : AlgebraicComplex, (minpoly AlgebraicComplex M).IsRoot a →
      ∃ q : ℚ, (q : AlgebraicComplex) = a) :
    ∃ N : ℕ, 0 < N ∧
      ∃ Y : (Matrix n n (LaurentLogBase AlgebraicComplex))ˣ,
        matrixDerivative (manuscriptBaseDerivation (k := AlgebraicComplex) N)
          (Y : Matrix n n (LaurentLogBase AlgebraicComplex)) =
          ramifiedConstantMatrix M * (Y : Matrix n n (LaurentLogBase AlgebraicComplex)) ∧
        (laurentLogBasePoint AlgebraicComplex).toRingHom.mapMatrix
          (Y : Matrix n n (LaurentLogBase AlgebraicComplex)) = 1 := by
  letI : IsAlgClosed AlgebraicComplex := algebraicComplex_isAlgClosed
  exact stage15_rational_matrix_fundamental_unit M hrat
end StrictEUnit
#print axioms StrictEUnit.algebraicComplex_isAlgClosed
#print axioms StrictEUnit.algebraicComplex_rational_matrix_fundamental_unit
