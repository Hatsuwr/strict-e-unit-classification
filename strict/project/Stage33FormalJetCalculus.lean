import Stage30ScalarJetIndependence
import FundamentalMatrixConstants

/-! Elementary ordinary-jet factorization in a differential field. The
recursion and scalar basis remain literal data; no frame inverse is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k E n : Type*} [Field k] [Field E] [Algebra k E]
  [Fintype n] [DecidableEq n]

/-- Multiplying the ordinary derivation x⁻¹D by x recovers the Euler derivation. -/
theorem stage33_euler_of_ordinary (D : Derivation k E E) (x : E) (hx : x ≠ 0)
    (a : E) : x * (x⁻¹ • D) a = D a := by
  change x * (x⁻¹ * D a) = D a
  rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]

/-- Euler differentiation of a positive coordinate power. -/
theorem stage33_euler_pow (D : Derivation k E E) (x : E) (hDx : D x = x)
    (i : ℕ) : D (x ^ i) = (i : E) * x ^ i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [D.leibniz_pow, hDx]
    simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    rw [pow_succ]

/-- The product of a recursive row with a constant-residue solution has the
falling-Euler recurrence. This is only the finite Leibniz computation. -/
theorem stage33_row_product_recurrence (D : Derivation k E E)
    (C Z : Matrix n n E) (U : ℕ → n → E)
    (hU : ∀ i j, U (i + 1) j = D (U i j) + ∑ l, U i l * C l j - (i : E) * U i j)
    (hZ : matrixDerivative D Z = C * Z) (i : ℕ) (j : n) :
    ∑ l, U (i + 1) l * Z l j =
      D (∑ l, U i l * Z l j) - (i : E) * ∑ l, U i l * Z l j := by
  have hZe (l : n) : D (Z l j) = ∑ a, C l a * Z a j :=
    congrFun (congrFun hZ l) j
  simp only [hU, map_sum, D.leibniz, smul_eq_mul, hZe,
    add_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  have hdouble : (∑ l, ∑ a, U i a * C a l * Z l j) =
      ∑ l, ∑ a, U i l * (C l a * Z a j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hdouble]
  congr 1
  · ac_rfl
  · apply Finset.sum_congr rfl
    intro l hl
    ring

/-- The numerator of the ith literal ordinary jet is the ith recursive row
product. No change to the original scalar row occurs. -/
theorem stage33_ordinary_jet_numerator (D : Derivation k E E)
    (x : E) (hx : x ≠ 0) (hDx : D x = x)
    (C Z : Matrix n n E) (U : ℕ → n → E)
    (hU : ∀ i j, U (i + 1) j = D (U i j) + ∑ l, U i l * C l j - (i : E) * U i j)
    (hZ : matrixDerivative D Z = C * Z) (i : ℕ) (j : n) :
    x ^ i * ((x⁻¹ • D : Derivation k E E) : E → E)^[i]
        (∑ l, U 0 l * Z l j) = ∑ l, U i l * Z l j := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [stage33_row_product_recurrence D C Z U hU hZ, ← ih]
    rw [D.leibniz, stage33_euler_pow D x hDx]
    rw [Function.iterate_succ_apply']
    have hd := stage33_euler_of_ordinary D x hx
      (((x⁻¹ • D : Derivation k E E) : E → E)^[i] (∑ l, U 0 l * Z l j))
    simp only [smul_eq_mul]
    rw [← hd, pow_succ]
    ring

/-- With one common shift s=m-1, the matrix of ordinary jets is exactly the
pole-cleared row matrix times x⁻ˢZ. -/
theorem stage33_ordinary_jet_factorization (D : Derivation k E E)
    (x : E) (hx : x ≠ 0) (hDx : D x = x) (m : ℕ)
    (C Z : Matrix (Fin m) (Fin m) E) (U : ℕ → Fin m → E)
    (hU : ∀ i j, U (i + 1) j = D (U i j) + ∑ l, U i l * C l j - (i : E) * U i j)
    (hZ : matrixDerivative D Z = C * Z) :
    Matrix.of (fun i j : Fin m =>
      (((x⁻¹ • D : Derivation k E E) : E → E)^[i.val]) (∑ l, U 0 l * Z l j)) =
    (Matrix.of (fun i j : Fin m => x ^ (m - 1 - i.val) * U i.val j)) *
      ((x ^ (m - 1))⁻¹ • Z) := by
  ext i j
  have hi : (m - 1 - i.val) + i.val = m - 1 := by omega
  apply mul_left_cancel₀ (pow_ne_zero i.val hx)
  simp only [Matrix.of_apply]
  rw [stage33_ordinary_jet_numerator D x hx hDx C Z U hU hZ]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hp : x ^ i.val * x ^ (m - 1 - i.val) = x ^ (m - 1) := by
    rw [← pow_add, Nat.add_comm, hi]
  calc
    U i.val l * Z l j =
        (x ^ (m - 1) * (x ^ (m - 1))⁻¹) * (U i.val l * Z l j) := by
          rw [mul_inv_cancel₀ (pow_ne_zero _ hx), one_mul]
    _ = x ^ i.val * (x ^ (m - 1 - i.val) * U i.val l *
        ((x ^ (m - 1))⁻¹ * Z l j)) := by rw [← hp]; ring

/-- The inverse clearing power has the expected shifted Euler residue. -/
theorem stage33_euler_inv_pow (D : Derivation k E E) (x : E)
    (hx : x ≠ 0) (hDx : D x = x) (s : ℕ) :
    D ((x ^ s)⁻¹) = -(s : E) * (x ^ s)⁻¹ := by
  rw [D.leibniz_inv, stage33_euler_pow D x hDx]
  simp only [smul_eq_mul]
  field_simp
  <;> ring

/-- Scalar shifting produces the literal shifted constant-matrix equation. -/
theorem stage33_shifted_matrix_ode (D : Derivation k E E) (x : E)
    (hx : x ≠ 0) (hDx : D x = x) (s : ℕ) (C Z : Matrix n n E)
    (hZ : matrixDerivative D Z = C * Z) :
    matrixDerivative D ((x ^ s)⁻¹ • Z) =
      (C - algebraMap E (Matrix n n E) (s : E)) * ((x ^ s)⁻¹ • Z) := by
  rw [Matrix.sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  ext i j
  have hZe : D (Z i j) = ∑ l, C i l * Z l j := congrFun (congrFun hZ i) j
  simp only [matrixDerivative_apply, Matrix.smul_apply, smul_eq_mul,
    D.leibniz, stage33_euler_inv_pow D x hx hDx, hZe, Matrix.sub_apply,
    Matrix.mul_apply, Finset.mul_sum]
  have hs : (∑ l, (x ^ s)⁻¹ * (C i l * Z l j)) =
      ∑ l, C i l * ((x ^ s)⁻¹ * Z l j) := by
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hs]
  ring

/-- Cancelling a genuine right matrix unit derives the frame equation. -/
theorem stage33_frame_ode_of_factorization (D : Derivation k E E)
    (B C F : Matrix n n E) (Z : (Matrix n n E)ˣ)
    (hY : matrixDerivative D (F * Z.val) = B * (F * Z.val))
    (hZ : matrixDerivative D Z.val = C * Z.val) :
    matrixDerivative D F = B * F - F * C := by
  rw [matrixDerivative_mul, hZ, ← mul_assoc, ← mul_assoc, ← add_mul] at hY
  have hcancel := congrArg (fun A : Matrix n n E => A * (↑Z⁻¹ : Matrix n n E)) hY
  simp only [mul_assoc, Units.mul_inv, mul_one] at hcancel
  exact eq_sub_of_add_eq hcancel

end StrictEUnit
