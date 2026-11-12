import SelectedAmplitudeSourcePreimages

noncomputable section
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

theorem shiftedPolynomialDerivative_field_map (φ : K →+* L) (c : K) (p : Polynomial K) :
    (shiftedPolynomialDerivative c p).map φ=shiftedPolynomialDerivative (φ c) (p.map φ) := by
  simp [shiftedPolynomialDerivative_apply,Polynomial.smul_eq_C_mul,Polynomial.derivative_map]

theorem polynomialShiftInverse_field_map (φ : K →+* L) (c : K) (hc : c≠0) (p : Polynomial K) :
    (polynomialShiftInverse c p).map φ=polynomialShiftInverse (φ c) (p.map φ) := by
  apply shiftedPolynomialDerivative_injective (φ c) ((map_ne_zero φ).mpr hc)
  rw [← shiftedPolynomialDerivative_field_map,polynomialShiftInverse_rightInverse c hc,
    polynomialShiftInverse_rightInverse (φ c) ((map_ne_zero φ).mpr hc)]

theorem logMixingForward_field_map (φ : K →+* L) (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (n : ℕ) (p : Polynomial K) :
    (logMixingForward rho n p).map φ=logMixingForward (φ rho) n (p.map φ) := by
  induction n with
  | zero =>rfl
  | succ n ih =>
    rw [logMixingForward,polynomialShiftInverse_field_map φ _ (h n),ih,logMixingForward]
    simp only [map_add,map_natCast]

theorem logMixingBackward_field_map (φ : K →+* L) (rho : K) (n : ℕ) (p : Polynomial K) :
    (logMixingBackward rho n p).map φ=logMixingBackward (φ rho) n (p.map φ) := by
  induction n with
  | zero =>rfl
  | succ n ih =>
    rw [logMixingBackward,shiftedPolynomialDerivative_field_map,ih,logMixingBackward]
    simp only [map_sub,map_natCast]

theorem logMixingMode_field_map (φ : K →+* L) (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (n : ℤ) (p : Polynomial K) :
    (logMixingMode rho n p).map φ=logMixingMode (φ rho) n (p.map φ) := by
  cases n with
  | ofNat n =>exact logMixingForward_field_map φ rho h n p
  | negSucc n =>exact logMixingBackward_field_map φ rho (n+1) p

def logCoefficientFieldMap (φ : K →+* L) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial L) := s.map (Polynomial.mapRingHom φ)

theorem generalizedLogLaplaceSeries_field_map (φ : K →+* L) (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0)
    (h' : ∀ n : ℕ,φ rho+(n+1:ℕ)≠0) (s : LaurentSeries (Polynomial K)) :
    logCoefficientFieldMap φ (generalizedLogLaplaceSeries rho h s)=
      generalizedLogLaplaceSeries (φ rho) h' (logCoefficientFieldMap φ s) := by
  apply HahnSeries.ext
  funext n
  change ((generalizedLogLaplaceSeries rho h s).coeff n).map φ=_
  simp only [logCoefficientFieldMap,HahnSeries.map_coeff,Polynomial.mapRingHom,
    generalizedLogLaplaceSeries_coeff,Polynomial.smul_eq_C_mul,Polynomial.map_mul,
    Polynomial.map_C,logMixingMode_field_map φ rho h,map_zpow₀,map_neg,map_one]
  rfl

end StrictEUnit
end
