import RetainedCoefficientStrictEFunction
import StrictEScalarFunctionClosure
import Stage15StrictECoordinate

noncomputable section
namespace StrictEUnit

theorem strictEFunction_naturalMonomial_mul {f : ℂ →ℂ}
    (hf : IsStrictEFunction f) (s : ℕ) :
    IsStrictEFunction (fun z =>z^s*f z) := by
  induction s with
  | zero => simpa only [pow_zero,one_mul] using hf
  | succ s ih =>
    have hprod : IsStrictEFunction (fun z =>z*(z^s*f z)) := by
      obtain ⟨a,hd,hs,ha⟩ := strictEFunction_mul_analytic_arithmetic strictEFunction_coordinate ih
      exact ⟨a,hd,hs,strictEFunction_mul_hasAlgebraicPolynomialODE strictEFunction_coordinate ih,ha⟩
    simpa only [pow_succ',mul_assoc] using hprod

local instance shiftedEntireCommRing :
    CommRing (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :=
  (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield).toCommRing

def naturalShiftEntire (s : ℕ)
    (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :
    subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
  subfieldEntireCoordinate (algebraicClosure ℚ ℂ).toSubfield ^ s * F

theorem naturalShiftEntire_strict (s : ℕ)
    (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (hF : IsStrictEFunction F.val.val) :
    IsStrictEFunction (naturalShiftEntire s F).val.val :=
  strictEFunction_naturalMonomial_mul hF s

theorem naturalShiftEntire_laurent (s : ℕ)
    (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :
    stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield (naturalShiftEntire s F)=
      HahnSeries.single (s:ℤ) (1:(algebraicClosure ℚ ℂ).toSubfield)*
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield F := by
  rw [naturalShiftEntire,map_mul,map_pow,stage14_subfieldEntireLaurentAlgHom_apply,
    subfieldEntireTaylorAlgHom_coordinate,HahnSeries.ofPowerSeries_X,HahnSeries.single_pow]
  simp only [nsmul_eq_mul,mul_one,one_pow]
end StrictEUnit
end
