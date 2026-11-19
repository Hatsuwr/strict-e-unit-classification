import FiniteLaurentConstantCoordinates

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def reflectedResidualConstant (d : ℕ) (P : Polynomial K) (j : ℕ) : LaurentSeries (Polynomial K) :=
  HahnSeries.single 0 (Polynomial.C ((-1:K)^((d:ℤ)-(j:ℤ))*P.coeff j))

theorem generalizedLogOrdinaryDerivative_constant (a : K) :
    generalizedLogOrdinaryDerivative 0 (HahnSeries.single 0 (Polynomial.C a))=0 := by
  apply HahnSeries.ext
  funext n
  simp only [generalizedLogOrdinaryDerivative,logMonomial_one_mul_coeff,
    twistedLogCoefficientEuler,shiftedPolynomialDerivative_apply,HahnSeries.coeff_single,HahnSeries.coeff_zero]
  split_ifs with h
  · have hn : n-(-1:ℤ)=0 := h
    rw [hn]
    simp
  · simp

theorem reflectedResidual_constant_expansion (d : ℕ) (P : Polynomial K) :
    logLaurentReflection (∑ j : Fin (P.natDegree+1),HahnSeries.single
      ((d:ℤ)-(j.val:ℤ)) (Polynomial.C (P.coeff j.val)))=
    ∑ j ∈ Finset.range (P.natDegree+1),
      logLaurentCoefficientMap (laurentIntegerMonomial ((d:ℤ)-(j:ℤ)))*reflectedResidualConstant d P j := by
  change logLaurentReflectionHom _=_
  rw [map_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  change logLaurentReflection _=_
  rw [logLaurentReflection_single,logLaurentCoefficientMap_integerMonomial]
  simp only [reflectedResidualConstant,HahnSeries.single_mul_single,add_zero,one_mul,
    Polynomial.smul_eq_C_mul,← map_mul]

/-- The actual zero-branch residual is absorbed by literal constant coordinates,
not by silently assuming its negative Laurent modes are polynomial forcing. -/
theorem reflectedResidual_constant_extension
    (n d : ℕ) (T : Polynomial K) (P : Polynomial K)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) (LaurentSeries K))
    (x : Fin (n+1) →LaurentSeries (Polynomial K))
    (hx : ∀ i,generalizedLogOrdinaryDerivative 0 (x i)=
      (∑ j,logLaurentCoefficientMap (A i j)*x j)+
      (if i.val=n then logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*
        logLaurentReflection (∑ j : Fin (P.natDegree+1),HahnSeries.single
          ((d:ℤ)-(j.val:ℤ)) (Polynomial.C (P.coeff j.val))) else 0)) :
    let v := parallelForcingVector x (reflectedResidualConstant d P) (P.natDegree+1)
    ∀ i,generalizedLogOrdinaryDerivative 0 (v i)=
      (Matrix.map (finiteLaurentForcingConnection A (clearedSourceForcingColumn n T)
        (fun j =>(d:ℤ)-(j:ℤ)) (P.natDegree+1)) logLaurentCoefficientMap).mulVec v i := by
  apply (finiteLaurentForcingConnection_mapped_equation_iff logLaurentCoefficientMap
    (generalizedLogOrdinaryDerivative 0) A (clearedSourceForcingColumn n T)
    (fun j =>(d:ℤ)-(j:ℤ)) x (reflectedResidualConstant d P) (P.natDegree+1)).mpr
  constructor
  · intro i
    rw [hx i,← reflectedResidual_constant_expansion]
    change _=(∑ j,logLaurentCoefficientMap (A i j)*x j)+_
    congr 1
    simp only [clearedSourceForcingColumn]
    by_cases hi : i.val=n
    · simp [hi]
    · have hi' : i.val+1≠n+1 := by omega
      simp [hi,hi']
  · intro j hj
    exact generalizedLogOrdinaryDerivative_constant _

end StrictEUnit
end
