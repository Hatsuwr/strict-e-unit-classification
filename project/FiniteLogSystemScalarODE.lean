import ActualLogCoefficientConnection
import FiniteConnectionScalarElimination
import Stage14LaurentPolynomialODEClosure

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The inverse coordinate is the actual rational-function image. -/
theorem rationalLaurent_inverse_coordinate :
    algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.X⁻¹)=HahnSeries.single (-1:ℤ) (1:K) := by
  rw [map_inv₀]
  change (((RatFunc.X:RatFunc K):LaurentSeries K))⁻¹=_
  rw [RatFunc.coe_X]
  apply inv_eq_of_mul_eq_one_right
  simp only [HahnSeries.single_mul_single,add_neg_cancel,one_mul,HahnSeries.single_zero_one]

/-- Every scalar log coefficient of an actual finite rational twisted-log
system has a nonzero polynomial ordinary ODE. The logarithmic degree bound
is finite and the off-diagonal log term is included in the stable span. -/
theorem finiteTwistedLogSystem_coefficient_polynomialODE
    {ι : Type*} [Fintype ι] (rho : K) (C : Matrix ι ι (RatFunc K))
    (y : ι →Polynomial (LaurentSeries K)) (d : ℕ)
    (hd : ∀ i,(y i).natDegree≤d)
    (hy : ∀ i,actualTwistedLogOrdinary rho (y i)=
      ∑ j,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (C i j))*y j) :
    ∀ i j,HasPolynomialScalarDifferentialRelation (k:=K) stage14_laurentAlgebraDerivation ((y i).coeff j) := by
  classical
  have hcoeff (i : ι) (j : ℕ) := actualTwistedLogOrdinary_log_coefficient rho (y i) j
  letI : SMul K (LaurentSeries K) := Algebra.toSMul
  letI : SMul K (RatFunc K) := Algebra.toSMul
  letI : Module K (LaurentSeries K) := Algebra.toModule
  letI : Module K (RatFunc K) := Algebra.toModule
  letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
  let M := Submodule.span (RatFunc K) (Set.range (fun ij : ι × Fin (d+1) =>(y ij.1).coeff ij.2.val))
  have hmem (i : ι) (j : ℕ) : (y i).coeff j∈M := by
    by_cases hj : j<d+1
    · exact Submodule.subset_span ⟨(i,⟨j,hj⟩),rfl⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hd i;omega)]
      exact Submodule.zero_mem _
  have hsmul (a : K) (i : ι) (j : ℕ) : HahnSeries.single (-1:ℤ) a*(y i).coeff j∈M := by
    have h := M.smul_mem ((algebraMap K (RatFunc K) a)*RatFunc.X⁻¹) (hmem i j)
    have he : algebraMap (RatFunc K) (LaurentSeries K)
        ((algebraMap K (RatFunc K) a)*RatFunc.X⁻¹)=HahnSeries.single (-1:ℤ) a := by
      rw [map_mul,← IsScalarTower.algebraMap_apply K (RatFunc K) (LaurentSeries K),
        rationalLaurent_inverse_coordinate,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
        HahnSeries.single_mul_single,zero_add,mul_one]
    simpa only [Algebra.smul_def,he] using h
  have hstable : ∀ f∈M,stage14_laurentAlgebraDerivation f∈M := by
    apply differential_span_stable stage14_rationalOrdinaryDerivation stage14_laurentAlgebraDerivation
      (fun b =>stage14_rationalLaurent_differential b)
    rintro f ⟨⟨i,j⟩,rfl⟩
    have he := congrArg (fun p : Polynomial (LaurentSeries K) =>p.coeff j.val) (hy i)
    dsimp only at he
    rw [hcoeff i j.val] at he
    simp only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul] at he
    have hrhs : (∑ l,algebraMap (RatFunc K) (LaurentSeries K) (C i l)*(y l).coeff j.val)∈M := by
      apply Submodule.sum_mem
      intro l hl
      simpa only [Algebra.smul_def] using M.smul_mem (C i l) (hmem l j.val)
    have hder := M.sub_mem (M.sub_mem hrhs (hsmul rho i j.val)) (hsmul ((j.val+1:ℕ):K) i (j.val+1))
    change laurentOrdinaryDerivation ((y i).coeff j.val)∈M
    convert hder using 1
    rw [← he]
    ring
  intro i j
  apply finiteDifferentialSpan_polynomialScalarRelation
  exact ⟨M,Submodule.fg_span (Set.finite_range _),hstable,hmem i j⟩
end StrictEUnit
end
