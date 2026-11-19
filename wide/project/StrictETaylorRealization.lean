import EntireSubfieldTaylorEmbedding
import StrictEFunctionDefinitions

/-!
The actual strict-E series supplies the arithmetic Taylor realization. The
conclusion is membership in the much larger algebra of entire functions with
algebraic Taylor coefficients, not strict-E ring closure or an arbitrary
formal-to-analytic realization.
-/
noncomputable section
namespace StrictEUnit

/-- A strict E-function is entire by its actual defining analytic condition. -/
theorem strictEFunction_differentiable {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    Differentiable ℂ f := by
  obtain ⟨a, hent, _⟩ := hf
  exact hent

/-- The strict-E series witness is exactly the factorial-normalized genuine
Cauchy coefficient sequence. -/
theorem strictEFunction_entireCauchyCoefficients {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) :
    ∃ a : ℕ → AlgebraicComplex, ∀ n : ℕ,
      entireCauchyCoefficient f n = (a n : ℂ) / (n.factorial : ℂ) := by
  obtain ⟨a, hent, hs, _⟩ := hf
  refine ⟨a, fun n => ?_⟩
  apply entireCauchyCoefficient_eq_of_hasSum hent
  intro z
  convert hs z using 1
  funext j
  ring

/-- Actual strict E-functions have algebraic ordinary Taylor coefficients;
this is derived from their factorial-normalized series, not assumed. -/
theorem strictEFunction_entireCauchyCoefficient_mem {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (n : ℕ) :
    entireCauchyCoefficient f n ∈ (algebraicClosure ℚ ℂ).toSubfield := by
  obtain ⟨a, ha⟩ := strictEFunction_entireCauchyCoefficients hf
  rw [ha n]
  exact (algebraicClosure ℚ ℂ).toSubfield.div_mem (a n).property
    (natCast_mem _ _)

/-- The actual function, with the arithmetic coefficient membership just proved. -/
def strictEFunctionTaylorRealization (f : ℂ → ℂ) (hf : IsStrictEFunction f) :
    subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
  ⟨⟨f, strictEFunction_differentiable hf⟩,
    (mem_subfieldEntireFunctionAlgebra _ _).mpr (strictEFunction_entireCauchyCoefficient_mem hf)⟩

@[simp] theorem strictEFunctionTaylorRealization_apply (f : ℂ → ℂ)
    (hf : IsStrictEFunction f) (z : ℂ) :
    (strictEFunctionTaylorRealization f hf).val.val z = f z := rfl

/-- The subfield-valued Taylor realization maps back to the genuine complex
Taylor series of the supplied strict E-function. -/
theorem strictEFunctionTaylorRealization_compatibility (f : ℂ → ℂ)
    (hf : IsStrictEFunction f) :
    PowerSeries.map (algebraicClosure ℚ ℂ).toSubfield.subtype
      (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization f hf)) = entireFormalTaylor f :=
  subfieldEntireTaylorAlgHom_compatibility _ _

/-- No two distinct actual strict E-functions acquire the same arithmetic
Taylor realization. -/
theorem strictEFunctionTaylorRealization_injective {f g : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hg : IsStrictEFunction g)
    (h : subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (strictEFunctionTaylorRealization f hf) =
      subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization g hg)) : f = g := by
  exact congrArg (fun u => u.val.val)
    (subfieldEntireTaylorAlgHom_injective _ h)

end StrictEUnit
