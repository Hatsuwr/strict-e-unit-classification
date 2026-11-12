import Stage33MappedJetFactorization
import Stage31RationalResidueShift
import Stage32FormalToActualFrame

/-! The common pole-clearing shift is a genuine ambient matrix unit; its
residue equation and rational spectrum are consequences, not new premises. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
local instance (k : Subfield ℂ) (n : Type*) : SMul (RatFunc (LaurentSeries k))
    (Matrix n n (RatFunc (LaurentSeries k))) := ⟨fun c A i j => c * A i j⟩

variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual unit x⁻ˢZbar in the established ambient matrix ring. -/
def stage33_shiftedFormalBaseUnit (N : ℕ) (hN : N ≠ 0) (s : ℕ)
    (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    (Matrix n n (RatFunc (LaurentSeries k)))ˣ :=
  Units.map (algebraMap (RatFunc (LaurentSeries k))
    (Matrix n n (RatFunc (LaurentSeries k)))).toMonoidHom
    (Units.mk0 ((stage17_ramifiedEntireFormalAlgHom k N hN
      (subfieldEntireCoordinate k)) ^ s)⁻¹
        (inv_ne_zero (pow_ne_zero s (stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN)))) *
    stage17_formalBaseMatrixUnit k Z

/-- The unit's entries are exactly the common scalar shift of the original Z. -/
theorem stage33_shiftedFormalBaseUnit_val (N : ℕ) (hN : N ≠ 0) (s : ℕ)
    (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    (stage33_shiftedFormalBaseUnit k N hN s Z).val =
      ((stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) ^ s)⁻¹ •
        (stage17_formalBaseMatrixUnit k Z).val := by
  simp only [stage33_shiftedFormalBaseUnit, Units.val_mul, Units.coe_map, Units.val_mk0,
    MonoidHom.coe_coe]
  change algebraMap (RatFunc (LaurentSeries k)) (Matrix n n (RatFunc (LaurentSeries k)))
    ((stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) ^ s)⁻¹) *
      (stage17_formalBaseMatrixUnit k Z).val = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- Residue shifting commutes with the exact coefficient embedding. -/
theorem stage33_shiftedResidue_map (M : Matrix n n k) (s : ℕ) :
    (stage33_shiftedResidue k M s).map (algebraMap k (RatFunc (LaurentSeries k))) =
      M.map (algebraMap k (RatFunc (LaurentSeries k))) -
        algebraMap (RatFunc (LaurentSeries k)) (Matrix n n (RatFunc (LaurentSeries k)))
          (s : RatFunc (LaurentSeries k)) := by
  ext i j
  simp only [stage33_shiftedResidue, Matrix.map_apply, Matrix.sub_apply, map_sub,
    Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

/-- The literal shifted unit satisfies the shifted residue equation. -/
theorem stage33_shiftedFormalBaseUnit_ode (N : ℕ) (hN : N ≠ 0) (s : ℕ)
    (M : Matrix n n k) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative (manuscriptBaseDerivation (k := k) N) Z.val =
      ramifiedConstantMatrix M * Z.val) :
    matrixDerivative (formalAmbientDerivation N hN)
      (stage33_shiftedFormalBaseUnit k N hN s Z).val =
      (stage33_shiftedResidue k M s).map (algebraMap k (RatFunc (LaurentSeries k))) *
        (stage33_shiftedFormalBaseUnit k N hN s Z).val := by
  rw [stage33_shiftedFormalBaseUnit_val, stage33_shiftedResidue_map]
  exact stage33_shifted_matrix_ode (formalAmbientDerivation N hN)
    (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))
    (stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN)
    (stage33_formalCoordinate_euler k N hN) s _ _
    (stage17_formalBaseMatrixUnit_ode k N hN M Z hZ)

/-- The common nonnegative shift preserves rational minimal-polynomial roots. -/
theorem stage33_shiftedResidue_rational (M : Matrix n n k) (s : ℕ)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∀ a : k, (minpoly k (stage33_shiftedResidue k M s)).IsRoot a →
      ∃ q : ℚ, (q : k) = a := by
  simpa only [stage33_shiftedResidue, Algebra.algebraMap_eq_smul_one] using
    stage31_natShift_rational_spectrum M s hrat

/-- The literal ordinary jet matrix of the defined scalar row. -/
def stage33_scalarNormalFormJet (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (e : Fin m → subfieldEntireFunctionAlgebra k)
    (Z : (Matrix (Fin m) (Fin m) (LaurentLogBase k))ˣ) :
    Matrix (Fin m) (Fin m) (RatFunc (LaurentSeries k)) :=
  Matrix.of (fun i j => stage30_derivativeJet
    (stage32_ramifiedOrdinaryDerivation k N hN) m (stage33_scalarNormalFormRow k N hN e Z j) i)

/-- Ordinary jets factor through the genuine shifted matrix unit. -/
theorem stage33_scalarNormalFormJet_factorization (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (e : Fin m → subfieldEntireFunctionAlgebra k) (M : Matrix (Fin m) (Fin m) k)
    (Z : (Matrix (Fin m) (Fin m) (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative (manuscriptBaseDerivation (k := k) N) Z.val =
      ramifiedConstantMatrix M * Z.val) :
    stage33_scalarNormalFormJet k N hN m e Z =
      stage17_formalFrame k N hN (stage33_entireJetFrame k m e M) *
        (stage33_shiftedFormalBaseUnit k N hN (m - 1) Z).val := by
  rw [stage33_shiftedFormalBaseUnit_val]
  exact stage33_mappedJet_factorization k N hN m e M Z hZ

end StrictEUnit
