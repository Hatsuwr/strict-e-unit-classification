import ActualEulerFieldMap
import FiniteSplittingUnfilteredFrame

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Integral multipliers descend along an injective field map, so the finite
splitting field does not add an arithmetic hypothesis on the solution. -/
theorem logSeriesPrefixArithmetic_field_descent (phi : K →+* L)
    (u : LaurentSeries (Polynomial K))
    (h : LogSeriesPrefixArithmetic (logCoefficientFieldHom phi u)) :
    LogSeriesPrefixArithmetic u := by
  obtain ⟨B,hB,hd⟩ := h
  refine ⟨B,hB,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hd N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm t
  apply (isIntegral_algHom_iff phi.toIntAlgHom phi.injective).mp
  have hi := hDi m hm t
  change IsIntegral ℤ ((D:L)*((u.coeff (m:ℤ)).map phi).coeff t) at hi
  simpa only [Polynomial.coeff_map,RingHom.toIntAlgHom_apply,map_mul,map_natCast] using hi

/-- A constructed finite splitting arithmetic frame suffices for every actual
solution over the original number field. The solution is explicitly mapped to
the frame field, and its integral multipliers descend back unchanged. -/
theorem finiteSplittingFrame_actual_solution_arithmetic {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hf : FiniteSplittingUnfilteredFrameData C) (xi : K)
    (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j) :
    ∀ i,LogSeriesPrefixArithmetic (u i) := by
  obtain ⟨b,hb,hNF,hfd,rho,Y,hdet,hY,hrho,A,B,hB,hden⟩ := hf
  let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
  let F := P.SplittingField
  letI : NumberField F :=hNF
  let phi : K →+* F :=algebraMap K F
  have he := actualEuler_solution_field_map phi C xi u hu
  have ha := actualLogFrame_solution_component_arithmetic (C.map (PowerSeries.map phi))
    rho Y hY hdet A B hB hden (phi xi) (fun i =>logCoefficientFieldHom phi (u i)) he
  intro i
  exact logSeriesPrefixArithmetic_field_descent phi (u i) (ha i)

end StrictEUnit
end
