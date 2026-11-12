import MonomialEulerSolutionTransport
import GeneralizedLogOrdinaryProduct

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem generalizedLogEuler_monomial_step (rho : K) (w : ℕ)
    (v : LaurentSeries (Polynomial K)) :
    twistedLogCoefficientEuler rho (HahnSeries.single (w:ℤ) (1:Polynomial K)*v)=
      (w:LaurentSeries (Polynomial K))*(HahnSeries.single (w:ℤ) (1:Polynomial K)*v)+
      HahnSeries.single ((w+1:ℕ):ℤ) (1:Polynomial K)*generalizedLogOrdinaryDerivative rho v := by
  apply HahnSeries.ext
  funext n
  simp only [twistedLogCoefficientEuler,shiftedPolynomialDerivative_apply,
    logMonomial_one_mul_coeff,HahnSeries.coeff_add,generalizedLogOrdinaryDerivative]
  have he : n-((w+1:ℕ):ℤ)-(-1:ℤ)=n-(w:ℤ) := by omega
  rw [he]
  rw [show (w:LaurentSeries (Polynomial K))=HahnSeries.C (w:Polynomial K) by simp]
  have hc (a : Polynomial K) (f : LaurentSeries (Polynomial K)) :
      (HahnSeries.single (0:ℤ) a*f).coeff n=a*f.coeff n := by
    simpa using (HahnSeries.coeff_single_mul_add (0:ℤ) n a f)
  rw [HahnSeries.C_apply,hc,logMonomial_one_mul_coeff]
  simp only [Polynomial.smul_eq_C_mul]
  push_cast
  simp only [map_add,map_sub,map_natCast,map_intCast]
  ring

/-- The exact gauge matrix action after any coefficient ring map. -/
theorem monomialEulerConnection_mapped_weighted_action {R : Type*} [CommRing R]
    (φ : LaurentSeries K →+* R) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (v : Fin r → R) (i : Fin r) :
    (∑ j,φ (monomialEulerConnection A w i j)*(φ (laurentIntegerMonomial (w j:ℤ))*v j))=
      (w i:R)*(φ (laurentIntegerMonomial (w i:ℤ))*v i)+
      φ (laurentIntegerMonomial ((w i+1:ℕ):ℤ))*(∑ j,φ (A i j)*v j) := by
  have ht (j : Fin r) : φ (monomialEulerConnection A w i j)*(φ (laurentIntegerMonomial (w j:ℤ))*v j)=
      (if i=j then (w i:R)*(φ (laurentIntegerMonomial (w i:ℤ))*v i) else 0)+
      φ (laurentIntegerMonomial ((w i+1:ℕ):ℤ))*(φ (A i j)*v j) := by
    have hm : φ (laurentIntegerMonomial ((w i:ℤ)+1-(w j:ℤ)))*φ (laurentIntegerMonomial (w j:ℤ))=
        φ (laurentIntegerMonomial ((w i+1:ℕ):ℤ)) := by
      rw [← map_mul,laurentIntegerMonomial_mul]
      congr 2;push_cast;omega
    simp only [monomialEulerConnection,map_add,map_mul,map_natCast,Matrix.one_apply]
    by_cases hij : i=j
    · subst j
      simp only [ite_true,map_one,mul_one]
      linear_combination (φ (A i i)*v i)*hm
    · simp only [hij,ite_false,map_zero,mul_zero,zero_mul,zero_add]
      calc
        _=(φ (laurentIntegerMonomial ((w i:ℤ)+1-(w j:ℤ)))*φ (laurentIntegerMonomial (w j:ℤ)))*(φ (A i j)*v j) := by ring
        _=_ := by rw [hm]
  simp_rw [ht]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.mul_sum]

theorem logLaurentCoefficientMap_integerMonomial (k : ℤ) :
    logLaurentCoefficientMap (laurentIntegerMonomial (K:=K) k)=HahnSeries.single k (1:Polynomial K) := by
  apply HahnSeries.ext
  funext n
  simp only [logLaurentCoefficientMap_coeff,laurentIntegerMonomial,HahnSeries.coeff_single]
  split_ifs <;> simp

/-- Regular Euler transport for generalized logarithmic solutions; rho and all
logarithmic coefficients are retained. No analytic interpretation is asserted. -/
theorem generalizedMonomialEulerPresentation_solution_iff {r : ℕ}
    (rho : K) (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hreal : monomialEulerConnection A w=C.map (HahnSeries.ofPowerSeries ℤ K))
    (v : Fin r → LaurentSeries (Polynomial K)) :
    (∀ i,generalizedLogOrdinaryDerivative rho (v i)=∑ j,logLaurentCoefficientMap (A i j)*v j) ↔
      ∀ i,twistedLogCoefficientEuler rho (HahnSeries.single (w i:ℤ) (1:Polynomial K)*v i)=
        ∑ j,logLaurentCoefficientMap (HahnSeries.ofPowerSeries ℤ K (C i j))*
          (HahnSeries.single (w j:ℤ) (1:Polynomial K)*v j) := by
  have hsum (i : Fin r) := monomialEulerConnection_mapped_weighted_action logLaurentCoefficientMap A w v i
  rw [hreal] at hsum
  simp only [Matrix.map_apply,logLaurentCoefficientMap_integerMonomial] at hsum
  constructor
  · intro h i
    rw [generalizedLogEuler_monomial_step,h i]
    exact (hsum i).symm
  · intro h i
    have hi := h i
    rw [generalizedLogEuler_monomial_step,hsum i] at hi
    have hh := congrArg (fun x =>HahnSeries.single (-((w i+1:ℕ):ℤ)) (1:Polynomial K)*x) (add_left_cancel hi)
    simpa only [← mul_assoc,HahnSeries.single_mul_single,neg_add_cancel,mul_one,HahnSeries.single_zero_one,one_mul] using hh

end StrictEUnit
end
