import RamifiedBaseManuscriptODE
import Mathlib.Data.Rat.Lemmas

/-! Finite rational exponent lists admit actual common positive ramification
weights. This does not supply eigenvalues or a Jordan basis for a matrix. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Clearing all denominators at once gives positive ramification and actual
integer weights for any finite list of rational exponents. -/
theorem rational_weights_common_denominator {n : Type*} [Fintype n] (q : n → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : n → ℤ, ∀ i, (m i : ℚ) / (N : ℚ) = q i := by
  classical
  let N : ℕ := ∏ i, (q i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hd : ∀ i, (q i).den ∣ N := fun i =>
    Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
  choose a ha using hd
  refine ⟨N, hN, fun i => (q i).num * (a i : ℤ), fun i => ?_⟩
  apply (div_eq_iff (show (N : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr (ne_of_gt hN))).mpr
  rw [Int.cast_mul, Int.cast_natCast, ha i, Nat.cast_mul, ← mul_assoc,
    Rat.mul_den_eq_num]

/-- The same denominator and weights are compatible with any characteristic-zero
coefficient field, and equality of the weights is exactly equality of exponents. -/
theorem rational_weights_common_denominator_field {k n : Type*}
    [Field k] [CharZero k] [Fintype n] (q : n → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : n → ℤ,
      (∀ i, (m i : k) / (N : k) = (q i : k)) ∧
      (∀ i j, m i = m j ↔ q i = q j) := by
  obtain ⟨N, hN, m, hm⟩ := rational_weights_common_denominator q
  refine ⟨N, hN, m, ?_, ?_⟩
  · intro i
    exact_mod_cast hm i
  · intro i j
    constructor
    · intro hij
      rw [← hm i, ← hm j, hij]
    · intro hij
      have heq : (m i : ℚ) / (N : ℚ) = (m j : ℚ) / (N : ℚ) := by rw [hm i, hm j, hij]
      have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
      exact_mod_cast (div_left_inj' hNQ).mp heq

/-- For supplied rational exponents and a compatible nilpotent block, the
ramification integer and weights can now be constructed rather than assumed. -/
theorem rational_ramified_base_matrix_exists {k n : Type*}
    [Field k] [CharZero k] [Fintype n] [DecidableEq n]
    (q : n → ℚ) (J : Matrix n n k) (hJ : IsNilpotent J)
    (hweight : ∀ i j, q i ≠ q j → J i j = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : n → ℤ,
      (∀ i, (m i : k) / (N : k) = (q i : k)) ∧
      matrixDerivative (manuscriptBaseDerivation (k := k) N)
        (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) =
        (Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) (q i : k)) +
          ramifiedConstantMatrix J) *
        (ramifiedBaseMatrix m J hJ : Matrix n n (LaurentLogBase k)) := by
  obtain ⟨N, hN, m, hm, heq⟩ := rational_weights_common_denominator_field (k := k) q
  refine ⟨N, hN, m, hm, ?_⟩
  have hw : RespectsRamifiedWeights m J := by
    intro i j hij
    exact hweight i j (fun h => hij ((heq i j).mpr h))
  simpa only [hm] using ramifiedBaseMatrix_manuscript_derivative N (ne_of_gt hN) m J hJ hw
/-- For rational diagonal exponents the block support condition is exactly
commutation, including when the coefficient field is larger than the rationals. -/
theorem rational_weight_support_iff_commute {k n : Type*}
    [Field k] [CharZero k] [Fintype n] [DecidableEq n]
    (q : n → ℚ) (J : Matrix n n k) :
    (∀ i j, q i ≠ q j → J i j = 0) ↔
      Commute (Matrix.diagonal fun i => (q i : k)) J := by
  constructor
  · intro h
    change Matrix.diagonal _ * J = J * Matrix.diagonal _
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : q i = q j
    · rw [hij, mul_comm]
    · rw [h i j hij, mul_zero, zero_mul]
  · intro h i j hij
    by_contra hJij
    have he := congrArg (fun A : Matrix n n k => A i j) h.eq
    dsimp only at he
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (J i j)] at he
    exact hij (Rat.cast_inj.mp (mul_right_cancel₀ hJij he))

/-- A commuting rational diagonal/nilpotent decomposition supplies an actual
normalized base-ring fundamental unit after some positive ramification. -/
theorem rational_commuting_fundamental_unit {k n : Type*}
    [Field k] [CharZero k] [Fintype n] [DecidableEq n]
    (q : n → ℚ) (J : Matrix n n k) (hJ : IsNilpotent J)
    (hcomm : Commute (Matrix.diagonal fun i => (q i : k)) J) :
    ∃ N : ℕ, 0 < N ∧ ∃ Z : (Matrix n n (LaurentLogBase k))ˣ,
      matrixDerivative (manuscriptBaseDerivation (k := k) N) (Z : Matrix n n (LaurentLogBase k)) =
        (Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) (q i : k)) +
          ramifiedConstantMatrix J) * (Z : Matrix n n (LaurentLogBase k)) ∧
      (laurentLogBasePoint k).toRingHom.mapMatrix (Z : Matrix n n (LaurentLogBase k)) = 1 := by
  obtain ⟨N, hN, m, _, hode⟩ := rational_ramified_base_matrix_exists q J hJ
    ((rational_weight_support_iff_commute q J).mpr hcomm)
  exact ⟨N, hN, ramifiedBaseMatrix m J hJ, hode, ramifiedBaseMatrix_at_point m J hJ⟩

end StrictEUnit
#print axioms StrictEUnit.rational_weights_common_denominator
#print axioms StrictEUnit.rational_weights_common_denominator_field
#print axioms StrictEUnit.rational_ramified_base_matrix_exists
#print axioms StrictEUnit.rational_weight_support_iff_commute
#print axioms StrictEUnit.rational_commuting_fundamental_unit
