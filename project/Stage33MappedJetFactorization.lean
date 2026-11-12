import Stage33ScalarNormalFormRowData
import Stage33EntireJetRows
import Stage33FormalJetCalculus
import Stage17ConstructedFormalFundamental
import Stage32FormalToActualFrame

/-! Specialization of the ordinary-jet calculation to the genuine ramified
Taylor map and actual entire rows, not arbitrary formal input functions. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing
local instance (k : Subfield ℂ) : AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring))
local instance (k : Subfield ℂ) (m : ℕ) : SMul (RatFunc (LaurentSeries k))
    (Matrix (Fin m) (Fin m) (RatFunc (LaurentSeries k))) :=
  ⟨fun c A i j => c * A i j⟩
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

theorem stage33_mapped_shift_sum (N : ℕ) (hN : N ≠ 0)
    (y : n → RatFunc (LaurentSeries k)) (M : Matrix n n k) (i : ℕ) (j : n) :
    (∑ l, y l * algebraMap k (RatFunc (LaurentSeries k)) (stage33_shiftedResidue k M i l j)) =
      (∑ l, y l * algebraMap k (RatFunc (LaurentSeries k)) (M l j)) - (i : RatFunc (LaurentSeries k)) * y j := by
  have hm (l : n) : stage33_shiftedResidue k M i l j = M l j - (if l = j then (i : k) else 0) := by
    rw [stage33_shiftedResidue, Matrix.sub_apply, Matrix.algebraMap_matrix_apply]
    rfl
  simp_rw [hm, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ l, y l *
      algebraMap k (RatFunc (LaurentSeries k)) (if l = j then (i : k) else 0)) =
      (i : RatFunc (LaurentSeries k)) *
        y j := by
    simp only [apply_ite, map_natCast, map_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hs]

/-- The mapped actual recursion satisfies precisely the falling-Euler recurrence. -/
theorem stage33_mappedJetRow_succ (N : ℕ) (hN : N ≠ 0)
    (e : n → subfieldEntireFunctionAlgebra k) (M : Matrix n n k) (i : ℕ) (j : n) :
    stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M (i+1) j) =
      formalAmbientDerivation N hN
        (stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M i j)) +
      ∑ l, stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M i l) *
        algebraMap k (RatFunc (LaurentSeries k)) (M l j) -
      (i : RatFunc (LaurentSeries k)) *
        stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M i j) := by
  change stage17_ramifiedEntireFormalAlgHom k N hN
    (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (stage33_entireJetRow k e M i j) +
      ∑ l, stage33_entireJetRow k e M i l *
        algebraMap k (subfieldEntireFunctionAlgebra k) (stage33_shiftedResidue k M i l j)) = _
  have hd : stage17_ramifiedEntireFormalAlgHom k N hN
      (subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k (stage33_entireJetRow k e M i j)) =
      formalAmbientDerivation N hN
        (stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M i j)) :=
    (stage17_entireFormal_powerPullback_derivation k N hN _).symm
  have hsum (g : n → subfieldEntireFunctionAlgebra k) :
      stage17_ramifiedEntireFormalAlgHom k N hN (∑ l, g l) =
        ∑ l, stage17_ramifiedEntireFormalAlgHom k N hN (g l) :=
    map_sum (stage17_ramifiedEntireFormalAlgHom k N hN).toRingHom.toAddMonoidHom g Finset.univ
  have hadd (a b : subfieldEntireFunctionAlgebra k) :
      stage17_ramifiedEntireFormalAlgHom k N hN (a+b) =
        stage17_ramifiedEntireFormalAlgHom k N hN a + stage17_ramifiedEntireFormalAlgHom k N hN b :=
    (stage17_ramifiedEntireFormalAlgHom k N hN).toRingHom.map_add a b
  rw [hadd, hd, hsum]
  simp only [map_mul, AlgHom.commutes]
  rw [stage33_mapped_shift_sum k N hN]
  ring

/-- The actual ramified coordinate is an Euler eigenvector of eigenvalue one. -/
theorem stage33_formalCoordinate_euler (N : ℕ) (hN : N ≠ 0) :
    formalAmbientDerivation N hN
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) =
        stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) := by
  have h := stage17_entireFormal_powerPullback_derivation k N hN (subfieldEntireCoordinate k)
  simpa only [subfieldEntireFunctionDerivation_coordinate, mul_one] using h

/- The original scalar row is defined, not an extra independent matrix input. -/

/-- The exact ordinary-jet factorization for the actual entire frame. -/
theorem stage33_mappedJet_factorization (N : ℕ) (hN : N ≠ 0) (m : ℕ)
    (e : Fin m → subfieldEntireFunctionAlgebra k) (M : Matrix (Fin m) (Fin m) k)
    (Z : (Matrix (Fin m) (Fin m) (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative (manuscriptBaseDerivation (k := k) N) Z.val =
      ramifiedConstantMatrix M * Z.val) :
    Matrix.of (fun i j : Fin m =>
      ((stage32_ramifiedOrdinaryDerivation k N hN) :
          RatFunc (LaurentSeries k) → RatFunc (LaurentSeries k))^[i.val]
            (stage33_scalarNormalFormRow k N hN e Z j)) =
      stage17_formalFrame k N hN (stage33_entireJetFrame k m e M) *
        (((stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k)) ^
          (m - 1))⁻¹ • (stage17_formalBaseMatrixUnit k Z).val) := by
  have h := stage33_ordinary_jet_factorization (formalAmbientDerivation (k := k) N hN)
    (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))
    (stage17_ramifiedEntireFormal_coordinate_ne_zero k N hN)
    (stage33_formalCoordinate_euler k N hN) m
    (M.map (algebraMap k (RatFunc (LaurentSeries k)))) (stage17_formalBaseMatrixUnit k Z).val
    (fun i j => stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M i j))
    (stage33_mappedJetRow_succ k N hN e M)
    (stage17_formalBaseMatrixUnit_ode k N hN M Z hZ)
  have hF : (Matrix.of (fun i j : Fin m =>
      stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) ^
        (m - 1 - i.val) *
      stage17_ramifiedEntireFormalAlgHom k N hN (stage33_entireJetRow k e M i.val j))) =
      stage17_formalFrame k N hN (stage33_entireJetFrame k m e M) := by
    ext i j
    simp only [stage17_formalFrame, Matrix.map_apply, Matrix.of_apply,
      stage33_entireJetFrame, map_mul, map_pow]
  rw [← hF]
  simpa only [stage32_ramifiedOrdinaryDerivation, stage33_scalarNormalFormRow,
    stage33_entireJetRow] using h


end StrictEUnit
