import GeneralizedLogLaplaceNonintegerImage

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def generalizedLogLaplaceLinear (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) :
    LaurentSeries (Polynomial K) →ₗ[K] LaurentSeries (Polynomial K) where
  toFun := generalizedLogLaplaceSeries rho h
  map_add' s t := by
    apply HahnSeries.ext
    funext n
    simp only [generalizedLogLaplaceSeries_coeff,HahnSeries.coeff_add,
      logMixingMode_add rho h,smul_add]
  map_smul' a s := by
    apply HahnSeries.ext
    funext n
    simp only [generalizedLogLaplaceSeries_coeff,HahnSeries.coeff_smul,
      logMixingMode_smul rho a h,RingHom.id_apply]
    exact smul_comm _ _ _

def logSourceZ (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  HahnSeries.single (-1 : ℤ) (1 : Polynomial K)*s

def logTargetX (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  HahnSeries.single (1 : ℤ) (1 : Polynomial K)*s

def logTargetNegativeDerivative (rho : K) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial K) :=
  -(HahnSeries.single (-1 : ℤ) (1 : Polynomial K)*twistedLogCoefficientEuler rho s)

theorem generalizedLogLaplaceLinear_Z (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) :
    generalizedLogLaplaceLinear rho h (logSourceZ s)=
      logTargetNegativeDerivative rho (generalizedLogLaplaceLinear rho h s) := by
  apply HahnSeries.ext
  funext n
  change (generalizedLogLaplaceSeries rho h (logSourceZ s)).coeff n=_
  rw [logSourceZ,generalizedLogLaplaceSeries_z_coeff,logTargetNegativeDerivative,HahnSeries.coeff_neg]
  have hi : n=(n+1)+(-1) := by omega
  conv_rhs => arg 1;rw [hi,HahnSeries.coeff_single_mul_add,one_mul]
  simp only [twistedLogCoefficientEuler,Int.cast_add,Int.cast_one,add_assoc]
  rfl

theorem generalizedLogLaplaceLinear_Dz (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) :
    generalizedLogLaplaceLinear rho h (reciprocalLogSeriesDerivative rho s)=
      logTargetX (generalizedLogLaplaceLinear rho h s) := by
  apply HahnSeries.ext
  funext n
  change (generalizedLogLaplaceSeries rho h (reciprocalLogSeriesDerivative rho s)).coeff n=_
  rw [generalizedLogLaplaceSeries_Dz_coeff,logTargetX]
  have hi : n=(n-1)+1 := by omega
  conv_rhs => rw [hi,HahnSeries.coeff_single_mul_add,one_mul]
  rfl

end StrictEUnit
end
