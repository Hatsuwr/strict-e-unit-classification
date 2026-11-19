import ConstantForcingConnection
import LaurentPrefixProductArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
local instance : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective

/-- Dividing by a constant acts coefficientwise, without any pole shift. -/
theorem forcing_laurent_div_nat_coeff (x : LaurentSeries K) (m : ℕ) (l : ℤ) :
    (x/(m : LaurentSeries K)).coeff l=x.coeff l/(m : K) := by
  rw [div_eq_mul_inv,← map_natCast (HahnSeries.C : K →+* LaurentSeries K) m,
    ← map_inv₀,HahnSeries.C_apply,HahnSeries.coeff_mul_single_zero,div_eq_mul_inv]

theorem forcing_laurent_nat_mul_coeff (x : LaurentSeries K) (m : ℕ) (l : ℤ) :
    ((m : LaurentSeries K)*x).coeff l=(m : K)*x.coeff l := by
  rw [← map_natCast (HahnSeries.C : K →+* LaurentSeries K) m,
    HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul]

theorem forcing_laurent_scaled_derivative_coeff (x : LaurentSeries K) (a h m : ℕ) (l : ℤ) :
    (((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[h])
      ((a.factorial : LaurentSeries K)*x)/(m.factorial : LaurentSeries K)).coeff l=
        ((a.factorial : K)*(h.factorial : K)/(m.factorial : K))*
          (LaurentSeries.hasseDeriv K h x).coeff l := by
  rw [forcing_laurent_div_nat_coeff,← nsmul_eq_mul,
    laurentOrdinaryDerivation_eq_native,LaurentSeries.derivative_iterate,map_nsmul]
  simp only [nsmul_eq_mul]
  rw [forcing_laurent_nat_mul_coeff,forcing_laurent_nat_mul_coeff]
  ring

/-- Literal coefficient formula for the FULL divided forcing column. The
old divided matrix and the forcing entry appear only in a convolution. -/
theorem constantForcingColumn_divided_coeff {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (m : ℕ) (i : Fin r) (l : ℤ) :
    (constantForcingColumn (stage14_laurentAlgebraDerivation (k:=K)) A b m i/
        (m.factorial : LaurentSeries K)).coeff l=
      ∑ a ∈ Finset.range m,((a.factorial : K)*((m-1-a).factorial : K)/(m.factorial : K))*
        (LaurentSeries.hasseDeriv K (m-1-a)
          (∑ j,(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
            (a.factorial : LaurentSeries K))*b j)).coeff l := by
  rw [constantForcingColumn_sum,Finset.sum_div,HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he : (∑ j,matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j*b j)=
      (a.factorial : LaurentSeries K)*
        ∑ j,(matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
          (a.factorial : LaurentSeries K))*b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hf : (a.factorial : LaurentSeries K)≠0 := by
      exact_mod_cast (Nat.factorial_ne_zero a)
    field_simp
  rw [he]
  exact forcing_laurent_scaled_derivative_coeff _ a (m-1-a) m l

end StrictEUnit
end
