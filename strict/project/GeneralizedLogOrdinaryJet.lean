import ParallelForcingMoments
import GeneralizedLogLaplaceDerivativeIdentity
import MinimalDifferentialCompanion

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Ordinary t derivative of the coefficient series after factoring t^rho. -/
def generalizedLogOrdinaryDerivative (rho : K) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial K) := HahnSeries.single (-1:ℤ) (1:Polynomial K)*twistedLogCoefficientEuler rho s

/-- The reciprocal derivative is converted by the exact -t^-2 factor.
This does not change or discard the external exponent or log terms. -/
theorem generalizedLogOrdinaryDerivative_from_reciprocal (rho : K)
    (s : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho s=
      -(HahnSeries.single (-2:ℤ) (1:Polynomial K)*reciprocalLogSeriesDerivative rho s) := by
  have hc (k n : ℤ) (f : LaurentSeries (Polynomial K)) :
      (HahnSeries.single k (1:Polynomial K)*f).coeff n=f.coeff (n-k) := by
    have he : n=(n-k)+k := by omega
    conv_lhs => rw [he]
    rw [HahnSeries.coeff_single_mul_add,one_mul]
  apply HahnSeries.ext
  funext n
  simp only [generalizedLogOrdinaryDerivative,reciprocalLogSeriesDerivative,HahnSeries.coeff_neg,hc,neg_neg]
  have he : n-(-1:ℤ)=(n-(-2:ℤ))-1 := by omega
  rw [he]

def generalizedLogOrdinaryJet (rho : K) (n : ℕ) (s : LaurentSeries (Polynomial K)) :
    Fin (n+1) →LaurentSeries (Polynomial K) := fun j =>(generalizedLogOrdinaryDerivative rho)^[j.val] s

/-- The generalized scalar residual and its canonical vector jet have exactly
the same forced companion equation. Identification of the actual reciprocal
source array with this scalar residual is a separate obligation. -/
theorem generalizedLogOrdinaryJet_forced_iff (rho : K) (n : ℕ)
    (c : Fin (n+1) →LaurentSeries K) (s F : LaurentSeries (Polynomial K)) :
    (∀ i,generalizedLogOrdinaryDerivative rho (generalizedLogOrdinaryJet rho n s i)=
      (∑ j,logLaurentCoefficientMap (minimalDerivativeCompanion (n+1) c i j)*generalizedLogOrdinaryJet rho n s j)+
        (if i.val=n then F else 0)) ↔
    (generalizedLogOrdinaryDerivative rho)^[n+1] s=
      (∑ j,logLaurentCoefficientMap (c j)*generalizedLogOrdinaryJet rho n s j)+F := by
  have hlast : ∀ j,logLaurentCoefficientMap (minimalDerivativeCompanion (n+1) c (Fin.last n) j)=logLaurentCoefficientMap (c j) := by
    intro j;simp [minimalDerivativeCompanion]
  have hshift : ∀ i : Fin n,(∑ j,logLaurentCoefficientMap (minimalDerivativeCompanion (n+1) c i.castSucc j)*
      generalizedLogOrdinaryJet rho n s j)=generalizedLogOrdinaryJet rho n s i.succ := by
    intro i
    rw [Finset.sum_eq_single i.succ]
    · simp [minimalDerivativeCompanion,show i.val+1<n+1 by omega]
    · intro j hj hne
      have hjv : j.val≠i.val+1 := fun heq =>hne (Fin.ext heq)
      simp [minimalDerivativeCompanion,show i.val+1<n+1 by omega,hjv]
    · intro h;exact (h (Finset.mem_univ _)).elim
  constructor
  · intro h
    simpa only [hlast,Fin.val_last,ite_true,generalizedLogOrdinaryJet,
      Function.iterate_succ_apply'] using h (Fin.last n)
  · intro h i
    cases i using Fin.lastCases with
    | last =>simpa only [hlast,Fin.val_last,ite_true,generalizedLogOrdinaryJet,
        Function.iterate_succ_apply'] using h
    | cast i =>
      rw [hshift i,if_neg (show i.castSucc.val≠n by exact Nat.ne_of_lt i.isLt),add_zero]
      simp only [generalizedLogOrdinaryJet,Fin.coe_castSucc,Fin.val_succ,Function.iterate_succ_apply']

end StrictEUnit
end
