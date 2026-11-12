import AllClassSolutionMatrixPrefix
import Mathlib.RingTheory.HahnSeries.Summable

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- At the first possible index of y, a log-free regular multiplier only
contributes its constant coefficient. -/
theorem regularLaurent_leading_product {R : Type*} [CommRing R]
    (x y : LaurentSeries R) (b : ℤ)
    (hx : ∀ k,k<0 →x.coeff k=0) (hy : ∀ k,k<b →y.coeff k=0) :
    (x*y).coeff b=x.coeff 0*y.coeff b := by
  let u := x-HahnSeries.single 0 (x.coeff 0)
  have hu : ∀ k : ℤ,k<1 →u.coeff k=0 := by
    intro k hk
    change (x-HahnSeries.single 0 (x.coeff 0)).coeff k=0
    rw [HahnSeries.coeff_sub,HahnSeries.coeff_single]
    by_cases h : k=0
    · subst k;simp
    · rw [if_neg h,hx k (by omega),sub_zero]
  have hz := laurentRing_product_prefix_zero u y 1 b hu hy b (by omega)
  have he : x=HahnSeries.single 0 (x.coeff 0)+u := by dsimp [u];abel
  calc
    (x*y).coeff b=((HahnSeries.single 0 (x.coeff 0)+u)*y).coeff b := congrArg (fun z =>(z*y).coeff b) he
    _=x.coeff 0*y.coeff b := by
      rw [add_mul,HahnSeries.coeff_add,HahnSeries.coeff_single_zero_mul,hz,add_zero]

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero polynomial log eigenvector of a first-order Euler residue has
no positive log degree. Both its eigenvalue and degree are derived. -/
theorem logFirstOrder_polynomial_eigenvector_constant (p : Polynomial K) (hp : p≠0)
    (a b : K) (h : a • p+p.derivative=b • p) :
    a=b ∧ p.natDegree=0 := by
  have hc := congrArg (fun f : Polynomial K =>f.coeff p.natDegree) h
  simp only [Polynomial.coeff_add,Polynomial.coeff_smul,smul_eq_mul,Polynomial.coeff_derivative,
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self p.natDegree),zero_mul,add_zero] at hc
  have hab : a=b := mul_right_cancel₀ (Polynomial.coeff_natDegree.trans_ne (Polynomial.leadingCoeff_ne_zero.mpr hp)) hc
  have hd : p.derivative=0 := by
    rw [hab] at h
    exact add_eq_left.mp h
  exact ⟨hab,Polynomial.natDegree_eq_zero_of_derivative_eq_zero hd⟩

/-- A regular first-order scalar log equation forces its leading coefficient
to be a nonzero CONSTANT polynomial. No logarithmic inverse is assumed. -/
theorem logFirstOrder_leading_coefficient_constant
    (f : Polynomial (LaurentSeries K)) (a : PowerSeries K) (hf : f≠0)
    (h : logPolynomialEuler 1 f=logPowerSeriesEmbedding a*f) :
    ∃ c : K,c≠0 ∧ (logPolynomialToCoefficientSeries f).leadingCoeff=Polynomial.C c := by
  let s := logPolynomialToCoefficientSeries f
  let x := logLaurentCoefficientMap (HahnSeries.ofPowerSeries ℤ K a)
  have hs : s≠0 := fun hz =>hf (logPolynomialToCoefficientSeries_injective (hz.trans (map_zero _).symm))
  have hp : s.coeff s.order≠0 := HahnSeries.coeff_order_ne_zero hs
  have he := congrArg logPolynomialToCoefficientSeries h
  rw [logPolynomialToCoefficientSeries_euler,map_mul] at he
  change polynomialCoefficientEuler 1 s=logPolynomialToCoefficientSeries (Polynomial.C (HahnSeries.ofPowerSeries ℤ K a))*s at he
  rw [logPolynomialToCoefficientSeries_C] at he
  change polynomialCoefficientEuler 1 s=x*s at he
  have hc := congrArg (fun z : LaurentSeries (Polynomial K) =>z.coeff s.order) he
  dsimp only at hc
  change (s.order : K) • s.coeff s.order+(1 : K) • (s.coeff s.order).derivative=(x*s).coeff s.order at hc
  simp only [one_smul] at hc
  rw [regularLaurent_leading_product x s s.order
    (by intro k hk;rw [show x.coeff k=Polynomial.C ((HahnSeries.ofPowerSeries ℤ K a).coeff k) from rfl,
      powerSeries_laurent_coeff_neg a k hk,map_zero])
    (fun k hk =>HahnSeries.coeff_eq_zero_of_lt_order hk)] at hc
  have hx0 : x.coeff 0=Polynomial.C (PowerSeries.coeff K 0 a) := by
    change Polynomial.C ((HahnSeries.ofPowerSeries ℤ K a).coeff ((0 : ℕ) : ℤ))=_
    rw [HahnSeries.ofPowerSeries_apply_coeff]
  rw [hx0] at hc
  rw [← Polynomial.smul_eq_C_mul] at hc
  have hdeg := (logFirstOrder_polynomial_eigenvector_constant _ hp _ _ hc).2
  have heq : s.coeff s.order=Polynomial.C ((s.coeff s.order).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  refine ⟨(s.coeff s.order).coeff 0,?_,?_⟩
  · intro hz
    apply hp
    rw [heq,hz,map_zero]
  · rw [HahnSeries.leadingCoeff_eq]
    exact heq

/-- The inverse exists in polynomial-valued Laurent series themselves, not
merely in a larger rational-function field in the log variable. -/
theorem logFirstOrder_coefficient_series_isUnit
    (f : Polynomial (LaurentSeries K)) (a : PowerSeries K) (hf : f≠0)
    (h : logPolynomialEuler 1 f=logPowerSeriesEmbedding a*f) :
    IsUnit (logPolynomialToCoefficientSeries f) := by
  obtain ⟨c,hc,hcoeff⟩ := logFirstOrder_leading_coefficient_constant f a hf h
  apply HahnSeries.isUnit_iff.mpr
  rw [hcoeff]
  exact (isUnit_iff_ne_zero.mpr hc).map Polynomial.C

end StrictEUnit
end
