import FiberTrivializationEquivariance
import TensorUnitCharacterReduction

/-! Scalar comparison of actual same-character units and compatibility with
actual algebraic fiber specialization. No numerical identification is asserted. -/
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
section Chart
variable {k S H : Type*} [CommRing k] [CommRing S] [CommRing H]
  [Algebra k S] [Bialgebra k H]

/-- The actual counit gives the scalar coefficient of a charted weight unit. -/
theorem chart_weight_unit_eq_counit_mul
    (e:S ≃ₐ[k] H) (ρ:S →ₐ[k] S ⊗[k] H)
    (hequiv:∀ s:S, numericalTensorChart e (ρ s) = Coalgebra.comul (R:=k) (e s))
    (u:Sˣ) (χ:Hˣ) (hu:ρ (u:S)=(u:S) ⊗ₜ[k] (χ:H)) :
    chartUnit e u = scalarUnit (counitUnit (k:=k) (chartUnit e u)) * χ := by
  apply Units.ext
  have h : Coalgebra.comul (R:=k) (e (u:S)) = e (u:S) ⊗ₜ[k] (χ:H) := by
    rw [← hequiv,hu,numericalTensorChart_tmul]
  exact (regular_weight_eq_counit_smul (χ:H) (e (u:S)) h).trans
    (Algebra.smul_def _ _)

/-- Same-character units differ by an actual scalar UNIT, via the derived
chart and counit. Neither a domain nor a grouplike premise is needed here. -/
theorem chart_same_weight_units_scalar_ratio
    (e:S ≃ₐ[k] H) (ρ:S →ₐ[k] S ⊗[k] H)
    (hequiv:∀ s:S, numericalTensorChart e (ρ s) = Coalgebra.comul (R:=k) (e s))
    (u v:Sˣ) (χ:Hˣ) (hu:ρ (u:S)=(u:S) ⊗ₜ[k] (χ:H))
    (hv:ρ (v:S)=(v:S) ⊗ₜ[k] (χ:H)) :
    ∃ a:kˣ, u = Units.map (algebraMap k S).toMonoidHom a * v := by
  let a := counitUnit (k:=k) (chartUnit e u)
  let b := counitUnit (k:=k) (chartUnit e v)
  have hu' := chart_weight_unit_eq_counit_mul e ρ hequiv u χ hu
  have hv' := chart_weight_unit_eq_counit_mul e ρ hequiv v χ hv
  have he : chartUnit e u = scalarUnit (H:=H) (a*b⁻¹) * chartUnit e v := by
    rw [hu',hv']
    change scalarUnit a * χ = scalarUnit (a*b⁻¹) * (scalarUnit b * χ)
    simp only [scalarUnit,map_mul,map_inv,mul_assoc,inv_mul_cancel_left]
  refine ⟨a*b⁻¹,?_⟩
  apply Units.ext
  apply e.injective
  have he' := congrArg (fun z:Hˣ => (z:H)) he
  change e (u:S) = e (algebraMap k S (↑(a*b⁻¹) : k) * (v:S))
  rw [map_mul,e.commutes]
  exact he'

end Chart

section Fiber
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k] [Algebra k H]

/-- The actual specialization map into the algebraic tensor fiber. -/
def algebraicFiberSpecialization : R →ₐ[k] k ⊗[B] R :=
  (Algebra.TensorProduct.includeRight : R →ₐ[B] k ⊗[B] R).restrictScalars k

/-- The mixed associator agrees with the actual specialization on tensor factors. -/
theorem fiberMixedAssoc_specialization (z:R ⊗[k] H) :
    (fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm ((1:k) ⊗ₜ[B] z) =
      Algebra.TensorProduct.map (algebraicFiberSpecialization (k:=k) (B:=B))
        (AlgHom.id k H) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add,map_add,hx,hy]
  | tmul r h => rfl

/-- Specialization intertwines the actual functional and fiber coactions. -/
theorem algebraicFiberSpecialization_coaction
    (e:R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (r:R) :
    algebraicFiberCoaction e (algebraicFiberSpecialization (k:=k) (B:=B) r) =
      Algebra.TensorProduct.map (algebraicFiberSpecialization (k:=k) (B:=B))
        (AlgHom.id k H) (inverseMultiplicationCoaction e r) := by
  rw [algebraicFiberCoaction_eq_baseChange]
  change fiberCoactionBaseChange (inverseMultiplicationCoaction e) ((1:k) ⊗ₜ[B] r) = _
  rw [fiberCoactionBaseChange_tmul,fiberMixedAssoc_specialization]

/-- A genuine functional weight equation remains the same weight on the fiber. -/
theorem algebraicFiberSpecialization_weight
    (e:R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (r:R) (h:H)
    (hr:inverseMultiplicationCoaction e r=r ⊗ₜ[k] h) :
    algebraicFiberCoaction e (algebraicFiberSpecialization (k:=k) (B:=B) r) =
      (algebraicFiberSpecialization (k:=k) (B:=B) r) ⊗ₜ[k] h := by
  rw [algebraicFiberSpecialization_coaction,hr]
  rfl
end Fiber
end StrictEUnit
#print axioms StrictEUnit.chart_weight_unit_eq_counit_mul
#print axioms StrictEUnit.chart_same_weight_units_scalar_ratio
#print axioms StrictEUnit.algebraicFiberSpecialization
#print axioms StrictEUnit.fiberMixedAssoc_specialization
#print axioms StrictEUnit.algebraicFiberSpecialization_coaction
#print axioms StrictEUnit.algebraicFiberSpecialization_weight
