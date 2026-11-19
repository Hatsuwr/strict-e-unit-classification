import LaurentForcingEulerAugmentation
import SelectedAmplitudeSourcePreimages

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem reciprocalPolynomial_finite_monomials (P : Polynomial K) :
    logLaurentCoefficientMap (signedLaplacePolynomialInZ P)=
      ∑ j : Fin (P.natDegree+1),HahnSeries.single (-(j.val:ℤ)) (Polynomial.C (P.coeff j.val)) := by
  let ev : Polynomial K →+* LaurentSeries K :=
    Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1:K))
  have he := congrArg ev (P.as_sum_range' (P.natDegree+1) (Nat.lt_succ_self _))
  change signedLaplacePolynomialInZ P=_ at he
  simp only [map_sum] at he
  have hm (j : ℕ) : ev (Polynomial.monomial j (P.coeff j))=
      HahnSeries.single (-(j:ℤ)) (P.coeff j) := signedLaplacePolynomialInZ_monomial _ _
  simp only [hm] at he
  rw [he,map_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  exact HahnSeries.map_single (Polynomial.C : K →+* Polynomial K).toZeroHom

/-- Exact finite forcing family after multiplying a reciprocal residual by
an arbitrary Laurent monomial. The exponent d-j is allowed to be negative. -/
theorem reciprocalResidual_shift_finite_monomials
    (s : LaurentSeries (Polynomial K)) (P : Polynomial K)
    (hs : ∀ k : ℤ,s.coeff k=if k≤0 then Polynomial.C (P.coeff (-k).toNat) else 0)
    (d : ℤ) :
    HahnSeries.single d (1:Polynomial K)*s=
      ∑ j : Fin (P.natDegree+1),HahnSeries.single (d-(j.val:ℤ)) (Polynomial.C (P.coeff j.val)) := by
  have he : s=logLaurentCoefficientMap (signedLaplacePolynomialInZ P) := by
    apply HahnSeries.ext
    funext k
    rw [hs,logLaurentCoefficientMap_coeff,signedLaplacePolynomialInZ_coeff]
    split_ifs <;> simp only [map_zero]
  rw [he,reciprocalPolynomial_finite_monomials,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [HahnSeries.single_mul_single,one_mul,sub_eq_add_neg]

/-- The zero-class preimage has a rigorously finite Laurent forcing family
for every subsequent integer gauge shift. No polynomial-forcing assumption. -/
theorem actualStage53_zero_source_finite_laurent_forcing {mu nu : ℕ}
    (a : Fin (mu+1) →Fin (nu+1) →K)
    (f : Polynomial (LaurentSeries K)) (hf : actualTwistedStage53Action 0 a f=0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=
        logPolynomialToCoefficientSeries f ∧
      (∀ n,(u.coeff n).natDegree≤f.natDegree+1) ∧
      ∃ P : Polynomial K,∀ d : ℤ,
        HahnSeries.single d (1:Polynomial K)*generalizedLogSourceArrayAction 0 a u=
          ∑ j : Fin (P.natDegree+1),HahnSeries.single (d-(j.val:ℤ)) (Polynomial.C (P.coeff j.val)) := by
  obtain ⟨u,hu,hd,hz,P,hP⟩ := actualStage53_zero_source_exists a f hf
  exact ⟨u,hu,hd,P,fun d =>reciprocalResidual_shift_finite_monomials _ P hP d⟩

end StrictEUnit
end
