import V5ActualBalanced132
import V5ActualKummerDifferential130
import V5LaurentEuler
import V5ActualKummerEuler129
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
theorem v5PowerEuler133 {K : Type*} [Field K] (q : ℕ) (p : LaurentPolynomial K) :
    v5BaseEuler132 (v5LaurentPower q p) =
      q • v5LaurentPower q (v5LaurentEulerLinear p) := by
  let F : LaurentPolynomial K →ₐ[K] LaurentPolynomial K :=
    { v5LaurentPower q with
      commutes' := by
          intro k
          change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C k) = _
          simp only [LaurentPolynomial.eval₂_C]
          rfl }
  have hc : v5BaseEuler132 (LaurentPolynomial.T 1 : LaurentPolynomial K) =
      LaurentPolynomial.T 1 := by
    rw [v5BaseEuler132_apply]
    change v5LaurentEulerLinear (Finsupp.single (1 : ℤ) (1 : K)) = _
    rw [v5LaurentEulerLinear_single]
    norm_num
  have h := v5_laurent_kummer_euler_compatibility F v5BaseEuler132 v5BaseEuler132
    (LaurentPolynomial.T 1) q hc hc (v5_laurentPower_coordinate129 q) p
  simpa only [v5BaseEuler132_apply, nsmul_eq_mul] using h
end StrictEUnit
#print axioms StrictEUnit.v5PowerEuler133
