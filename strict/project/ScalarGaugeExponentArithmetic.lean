import ResidueEigenvalueBinomialArithmetic
import CyclicRegularEulerFrame

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Every actual monic scalar indicial root has the explicit power eigenvector. -/
theorem monicScalarIndicial_root_eigenvector {r : ℕ}
    (b : Fin (r+1) →PowerSeries K) (hb : b (Fin.last r)=1) (xi : K)
    (hxi : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).eval xi=0) :
    (scalarEulerPowerSeriesCompanion r b).map (PowerSeries.constantCoeff K)*ᵥ
      (fun i : Fin r =>xi^i.val)=xi • (fun i : Fin r =>xi^i.val) := by
  have hs : (∑ j : Fin r,PowerSeries.constantCoeff K (b j.castSucc)*xi^j.val)+xi^r=0 := by
    simpa only [scalarEulerCoefficientSymbol,Polynomial.eval_add,Polynomial.eval_finset_sum,Polynomial.eval_monomial,
      Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last,PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hb,map_one,one_mul] using hxi
  have hs' : (∑ j : Fin r,PowerSeries.constantCoeff K (b j.castSucc)*xi^j.val)= -(xi^r) :=
    eq_neg_of_add_eq_zero_left hs
  funext i
  change (∑ j,PowerSeries.constantCoeff K (scalarEulerPowerSeriesCompanion r b i j)*xi^j.val)=xi*xi^i.val
  by_cases hi : i.val+1<r
  · let k : Fin r := ⟨i.val+1,hi⟩
    have hk (j : Fin r) : j.val=i.val+1 ↔ j=k :=
      ⟨fun h =>Fin.ext h,fun h =>congrArg Fin.val h⟩
    simp only [scalarEulerPowerSeriesCompanion,hi,if_true,hk,apply_ite,map_one,map_zero,
      ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact pow_succ' xi i.val
  · have he : i.val+1=r := by omega
    simp only [scalarEulerPowerSeriesCompanion,hi,if_false,hb,inv_one,one_mul,map_neg,neg_mul]
    rw [Finset.sum_neg_distrib,hs',neg_neg]
    exact (congrArg (fun m =>xi^m) he.symm).trans (pow_succ' xi i.val)

/-- Constant specialization of the PROVED differential gauge gives actual
residue conjugacy, since Euler differentiation has zero constant coefficient. -/
theorem regularScalarGauge_residue_intertwining {r : ℕ}
    (C B G : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=B*G) :
    (G.map (PowerSeries.constantCoeff K))*(C.map (PowerSeries.constantCoeff K))=
      (B.map (PowerSeries.constantCoeff K))*(G.map (PowerSeries.constantCoeff K)) := by
  funext i j
  have h := congrArg (PowerSeries.constantCoeff K) (congrFun (congrFun hc i) j)
  simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.map_apply,Matrix.of_apply,
    map_add,map_sum,map_mul,powerSeriesEuler_constantCoeff,zero_add] using h

/-- The constructed scalar exponents inherit binomial arithmetic from the
actual SOURCE connection, without a binomial-arithmetic premise. -/
theorem regularScalarGauge_indicial_binomial [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0<r) (hC : RegularEulerPrefixArithmetic C)
    (b : Fin (r+1) →PowerSeries K) (hb : b (Fin.last r)=1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G)
    (xi : K)
    (hxi : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).eval xi=0) :
    BinomialPrefixDenominators xi := by
  let C0 := C.map (PowerSeries.constantCoeff K)
  let B0 := (scalarEulerPowerSeriesCompanion r b).map (PowerSeries.constantCoeff K)
  let G0 := G.map (PowerSeries.constantCoeff K)
  let H0 := H.map (PowerSeries.constantCoeff K)
  have hGH0 : G0*H0=1 := by
    change (PowerSeries.constantCoeff K).mapMatrix G*(PowerSeries.constantCoeff K).mapMatrix H=1
    rw [← map_mul,hGH,map_one]
  have hHG0 : H0*G0=1 := by
    change (PowerSeries.constantCoeff K).mapMatrix H*(PowerSeries.constantCoeff K).mapMatrix G=1
    rw [← map_mul,hHG,map_one]
  have hc0 : G0*C0=B0*G0 := regularScalarGauge_residue_intertwining C _ G hc
  have hCH : C0*H0=H0*B0 := by
    calc
      _=H0*(G0*C0)*H0 := by rw [← mul_assoc,hHG0,one_mul]
      _=H0*(B0*G0)*H0 := by rw [hc0]
      _=(H0*B0)*(G0*H0) := by simp only [mul_assoc]
      _=_ := by rw [hGH0,mul_one]
  let w : Fin r →K := fun i =>xi^i.val
  let v := H0*ᵥw
  have hw : B0*ᵥw=xi • w := monicScalarIndicial_root_eigenvector b hb xi hxi
  have hv : C0*ᵥv=xi • v := by
    change C0*ᵥ(H0*ᵥw)=_
    rw [Matrix.mulVec_mulVec,hCH,← Matrix.mulVec_mulVec,hw,Matrix.mulVec_smul]
  have hGv : G0*ᵥv=w := by
    change G0*ᵥ(H0*ᵥw)=w
    rw [Matrix.mulVec_mulVec,hGH0,Matrix.one_mulVec]
  have hn : ∃ k,v k≠0 := by
    by_contra h
    push_neg at h
    have hz : v=0 := funext h
    have he := congrFun hGv ⟨0,hr⟩
    rw [hz,Matrix.mulVec_zero] at he
    have : (0 : K)=1 := by simpa [w] using he
    exact zero_ne_one this
  obtain ⟨k,hk⟩ := hn
  exact regularEulerPrefixArithmetic_eigenvalue C hC xi v hv k hk

end StrictEUnit
end
