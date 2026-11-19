import LogFrameConstructedInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem coefficientEuler_support_subset (s : LaurentSeries (Polynomial K)) :
    (polynomialCoefficientEuler 1 s).support ⊆ s.support := by
  intro n hn
  change s.coeff n≠0
  intro hz
  apply hn
  change (n:K) • s.coeff n+(1:K) • (s.coeff n).derivative=0
  simp [hz]

theorem coefficientLaurentEuler_mul (f g : LaurentSeries (Polynomial K)) :
    polynomialCoefficientEuler 1 (f*g)=
      polynomialCoefficientEuler 1 f*g+f*polynomialCoefficientEuler 1 g := by
  apply HahnSeries.ext
  funext n
  change (n:K) • (f*g).coeff n+(1:K) • ((f*g).coeff n).derivative=_
  rw [HahnSeries.coeff_add,HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (coefficientEuler_support_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (coefficientEuler_support_subset g)]
  simp only [one_smul,Finset.smul_sum,Polynomial.derivative_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1+ij.2=n := (Finset.mem_addAntidiagonal.mp hij).2.2
  change _=((ij.1:K) • f.coeff ij.1+(1:K) • (f.coeff ij.1).derivative)*g.coeff ij.2+
    f.coeff ij.1*((ij.2:K) • g.coeff ij.2+(1:K) • (g.coeff ij.2).derivative)
  rw [← hn,Int.cast_add,Polynomial.derivative_mul]
  simp only [one_smul,Polynomial.smul_eq_C_mul,map_add]
  ring

def coefficientEulerAdd : LaurentSeries (Polynomial K) →+ LaurentSeries (Polynomial K) where
  toFun := polynomialCoefficientEuler 1
  map_zero' := by ext n; simp [polynomialCoefficientEuler]
  map_add' f g := by
    apply HahnSeries.ext
    funext n
    change (n:K) • (f+g).coeff n+(1:K) • ((f+g).coeff n).derivative=_
    simp only [HahnSeries.coeff_add,Polynomial.derivative_add,smul_add]
    change _=((n:K) • f.coeff n+(1:K) • (f.coeff n).derivative)+
      ((n:K) • g.coeff n+(1:K) • (g.coeff n).derivative)
    abel

end StrictEUnit
end
