import FullArrayStage53Solutions

noncomputable section
open scoped BigOperators
namespace StrictEUnit
section Generic
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem connection_falling_iterate (E : Module.End K A) (u : ℤ → A)
    (hs : ∀ s y,u (-1)*E (u s*y)=u (s-1)*(E y+(s:K) • y))
    (i : ℤ) (j : ℕ) (y : A) :
    (fun v =>u (-1)*E v)^[j] (u i*y)=u (i-(j:ℤ))*
      (Polynomial.aeval E ((descPochhammer K j).comp (Polynomial.X+Polynomial.C (i:K)))) y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih,hs,logFourier_shiftedDesc_succ]
    have he : i-((j+1:ℕ):ℤ)=(i-(j:ℤ))-1 := by omega
    rw [he]
    simp only [map_mul,map_add,Polynomial.aeval_X,Polynomial.aeval_C,
      Module.End.mul_apply,LinearMap.add_apply,Module.algebraMap_end_apply,
      Int.cast_sub,Int.cast_natCast]

end Generic
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

def actualTwistedEulerEnd (rho : K) : Module.End K (Polynomial (LaurentSeries K)) where
  toFun f := stage61_logEulerDerivation 1 f + rho • f
  map_add' f g := by rw [map_add]; simp only [Algebra.smul_def]; ring
  map_smul' c f := by
    rw [Derivation.map_smul]
    simp only [RingHom.id_apply,Algebra.smul_def]
    ring

theorem actualTwistedEulerEnd_apply (rho : K) (f : Polynomial (LaurentSeries K)) :
    actualTwistedEulerEnd rho f=twistedLogPolynomialEuler rho f := by
  change stage38_sourceEuler 1 f+rho • f=_
  rw [stage38_sourceEuler_apply,twistedLogPolynomialEuler]
  simp only [Nat.cast_one,inv_one,← HahnSeries.C_apply,map_one,one_mul]

theorem actualTwistedLogOrdinary_euler (rho : K) :
    (actualTwistedLogOrdinary rho : _ → _)=
      fun f =>stage61_logZPow (K:=K) 1 (-1)*actualTwistedEulerEnd rho f := by
  funext f
  rw [actualTwistedLogOrdinary_shiftedEuler,actualTwistedEulerEnd_apply]
  simp only [frobeniusIntegerShift,stage61_logZPow,Nat.cast_one,one_mul]

theorem actualTwistedEuler_monomial_step (rho : K) (s : ℤ)
    (f : Polynomial (LaurentSeries K)) :
    stage61_logZPow (K:=K) 1 (-1)*actualTwistedEulerEnd rho (stage61_logZPow (K:=K) 1 s*f)=
      stage61_logZPow (K:=K) 1 (s-1)*(actualTwistedEulerEnd rho f+(s:K) • f) := by
  rw [actualTwistedEulerEnd_apply,actualTwistedEulerEnd_apply]
  simp only [stage61_logZPow,Nat.cast_one,one_mul]
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  change ((frobeniusIntegerShift (-1) (twistedLogPolynomialEuler rho (frobeniusIntegerShift s f))).coeff j).coeff n = _
  rw [frobeniusIntegerShift_coeff,twistedLogPolynomialEuler_double_coeff]
  simp only [frobeniusIntegerShift_coeff]
  change _=((frobeniusIntegerShift (s-1) (twistedLogPolynomialEuler rho f+(s:K) • f)).coeff j).coeff n
  rw [frobeniusIntegerShift_coeff,Polynomial.coeff_add,HahnSeries.coeff_add,
    twistedLogPolynomialEuler_double_coeff,frobenius_logScalar_double_coeff]
  have h : n-(-1)-s=n-(s-1) := by omega
  rw [h]
  simp only [Int.cast_sub,Int.cast_neg,Int.cast_one]
  ring

attribute [local irreducible] actualTwistedEulerEnd

theorem actualTwistedLogOrdinary_falling (rho : K) (i : ℤ) (j : ℕ)
    (f : Polynomial (LaurentSeries K)) :
    (actualTwistedLogOrdinary rho)^[j] (stage61_logZPow (K:=K) 1 i*f)=
      stage61_logZPow (K:=K) 1 (i-(j:ℤ))*(logFourier_endomorphismEval (actualTwistedEulerEnd rho)
        ((descPochhammer K j).comp (Polynomial.X+Polynomial.C (i:K))) f) := by
  rw [actualTwistedLogOrdinary_euler]
  exact connection_falling_iterate _ _ (actualTwistedEuler_monomial_step rho) i j f

end StrictEUnit
end
