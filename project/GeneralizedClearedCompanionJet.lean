import ActualPreimageOriginalSource
import OriginalSourceAugmentedIdentification

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The original same-clearing scalar tuple acts on generalized finite-log jets
by exactly T times the monic residual. -/
theorem generalizedSameCompanion_scalar_residual
    (rho : K) (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (G : LaurentSeries (Polynomial K)) :
    (∑ i : Fin ((n+1)+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U i))*
        (generalizedLogOrdinaryDerivative rho)^[i.val] G)=
    logLaurentCoefficientMap (polynomialLaurentImage T)*
      ((generalizedLogOrdinaryDerivative rho)^[n+1] G-
        ∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K) (c j))*
          generalizedLogOrdinaryJet rho n G j) := by
  have hidx : (⟨n+1-1,by omega⟩ : Fin (n+1))=Fin.last n := by apply Fin.ext;simp
  have hU : ∀ j,polynomialLaurentImage (U (Fin.last n) j)=polynomialLaurentImage T*
      algebraMap (RatFunc K) (LaurentSeries K) (c j) := by
    intro j
    simpa only [minimalDerivativeCompanion,Fin.val_last,lt_self_iff_false,ite_false] using
      same_companion_laurent_clearing n c T U hclear (Fin.last n) j
  rw [Fin.sum_univ_castSucc]
  simp only [sameCompanionScalarTuple,Fin.lastCases_castSucc,Fin.lastCases_last,
    Fin.coe_castSucc,Fin.val_last,hidx,map_neg,neg_mul,Finset.sum_neg_distrib,
    reciprocalGauge_aevalW]
  change (∑ j,-logLaurentCoefficientMap (polynomialLaurentImage (U (Fin.last n) j))*
      (generalizedLogOrdinaryDerivative rho)^[j.val] G)+
    logLaurentCoefficientMap (polynomialLaurentImage T)*(generalizedLogOrdinaryDerivative rho)^[n+1] G=_
  have hs : (∑ j,-logLaurentCoefficientMap (polynomialLaurentImage (U (Fin.last n) j))*
      (generalizedLogOrdinaryDerivative rho)^[j.val] G)=
      -logLaurentCoefficientMap (polynomialLaurentImage T)*
      ∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K) (c j))*
        generalizedLogOrdinaryJet rho n G j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hU,map_mul]
    unfold generalizedLogOrdinaryJet
    ring
  rw [hs]
  ring

/-- Normalize the exact residual using the genuine inverse of nonzero T in the
Laurent coefficient field, not an inverse invented in the polynomial-log ring. -/
theorem generalizedSameCompanion_scalar_iff
    (rho : K) (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (G F : LaurentSeries (Polynomial K)) :
    (∑ i : Fin ((n+1)+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U i))*
        (generalizedLogOrdinaryDerivative rho)^[i.val] G)=F ↔
    (generalizedLogOrdinaryDerivative rho)^[n+1] G=
      (∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K) (c j))*
        generalizedLogOrdinaryJet rho n G j)+
      logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*F := by
  rw [generalizedSameCompanion_scalar_residual rho n c T U hclear G]
  have hinv : logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*
      logLaurentCoefficientMap (polynomialLaurentImage T)=(1:LaurentSeries (Polynomial K)) := by
    rw [← map_mul,inv_mul_cancel₀ (polynomialLaurentImage_ne_zero T hT),map_one]
  constructor
  · intro he
    have hh := congrArg (fun s =>logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*s) he
    dsimp only at hh
    rw [← mul_assoc,hinv,one_mul] at hh
    exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
  · intro he
    rw [he,add_sub_cancel_left]
    rw [← mul_assoc,mul_comm _ (logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)),hinv,one_mul]

/-- Exact generalized canonical jet for the same cleared arithmetic companion. -/
theorem generalizedSameCompanion_jet_iff
    (rho : K) (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (G F : LaurentSeries (Polynomial K)) :
    (∀ i,generalizedLogOrdinaryDerivative rho (generalizedLogOrdinaryJet rho n G i)=
      (∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K)
        (minimalDerivativeCompanion (n+1) c i j))*generalizedLogOrdinaryJet rho n G j)+
        (if i.val=n then logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*F else 0)) ↔
    (∑ i : Fin ((n+1)+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U i))*
        (generalizedLogOrdinaryDerivative rho)^[i.val] G)=F := by
  have hc := originalSource_companion_laurent_map n c
  have he := generalizedLogOrdinaryJet_forced_iff rho n
    (fun j =>algebraMap (RatFunc K) (LaurentSeries K) (c j)) G
    (logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*F)
  rw [← hc] at he
  exact he.trans (generalizedSameCompanion_scalar_iff rho n c T U hT hclear G F).symm

end StrictEUnit
end
