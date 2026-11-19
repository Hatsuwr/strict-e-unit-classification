import ResonanceLogCoefficientFactorization
import Mathlib.RingTheory.Nilpotent.Exp

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]

def finiteLogMatrixGenerator (N : Matrix I I K) : Matrix I I (Polynomial K) :=
  (Polynomial.X : Polynomial K) • (Polynomial.C.mapMatrix N)

def finiteLogMatrixExponential (N : Matrix I I K) : Matrix I I (Polynomial K) :=
  IsNilpotent.exp (finiteLogMatrixGenerator N)

theorem finiteLogMatrixGenerator_nilpotent (N : Matrix I I K) (hN : IsNilpotent N) :
    IsNilpotent (finiteLogMatrixGenerator N) := by
  obtain ⟨d,hd⟩ := hN
  refine ⟨d,?_⟩
  simp only [finiteLogMatrixGenerator,smul_pow,← map_pow,hd,map_zero,smul_zero]

def finiteLogMatrixUnit (N : Matrix I I K) (hN : IsNilpotent N) :
    (Matrix I I (Polynomial K))ˣ :=
  (IsNilpotent.isUnit_exp (finiteLogMatrixGenerator_nilpotent N hN)).unit

@[simp] theorem finiteLogMatrixUnit_val (N : Matrix I I K) (hN : IsNilpotent N) :
    (finiteLogMatrixUnit N hN).val=finiteLogMatrixExponential N :=
  IsUnit.unit_spec _

theorem finiteLogMatrixExponential_coeff (N : Matrix I I K) (hN : IsNilpotent N)
    (i j : I) (d : ℕ) :
    (finiteLogMatrixExponential N i j).coeff d=(d.factorial:K)⁻¹*(N^d) i j := by
  obtain ⟨q,hq⟩ := hN
  have hg : (finiteLogMatrixGenerator N)^q=0 := by
    simp only [finiteLogMatrixGenerator,smul_pow,← map_pow,hq,map_zero,smul_zero]
  unfold finiteLogMatrixExponential
  rw [IsNilpotent.exp_eq_sum hg]
  simp only [Matrix.sum_apply,Matrix.smul_apply,finiteLogMatrixGenerator,smul_pow,
    ← map_pow,RingHom.mapMatrix_apply,Matrix.map_apply,Polynomial.finset_sum_coeff,
    Polynomial.coeff_smul,smul_eq_mul]
  have he (k : ℕ) : (Polynomial.X^k * Polynomial.C ((N^k) i j)).coeff d=
      if d=k then (N^k) i j else 0 := by
    rw [mul_comm,Polynomial.coeff_C_mul_X_pow]
  have hp (k : ℕ) : (N.map Polynomial.C)^k=(N^k).map Polynomial.C :=
    (map_pow Polynomial.C.mapMatrix N k).symm
  simp only [hp,Matrix.map_apply]
  simp only [he,apply_ite,mul_zero,smul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_range]
  by_cases hd : d<q
  · simp only [hd,if_true]
    simp only [Algebra.smul_def,map_inv₀,map_natCast]
  · simp only [hd,if_false]
    rw [pow_eq_zero_of_le (by omega) hq]
    simp
end StrictEUnit
end
