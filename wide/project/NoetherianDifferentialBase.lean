import LaurentLogBase
import Mathlib.Algebra.Module.FinitePresentation

/-! Concrete Noetherian and finite-presentation prerequisites for the future
finite differential-module projectivity argument. No projectivity is asserted. -/
noncomputable section
namespace StrictEUnit

/-- The exact abstract manuscript base is Noetherian: its Laurent coefficient
ring is a PID and hence Noetherian; adjoining the logarithmic polynomial variable
preserves Noetherianity. -/
theorem laurentLogBase_isNoetherianRing (k : Type*) [Field k] :
    IsNoetherianRing (LaurentLogBase k) := by infer_instance

/-- Finite modules over this actual base are finitely presented. This does not
imply projectivity without the remaining differential-module theorem. -/
theorem laurentLogBase_finitePresentation_of_finite (k M : Type*) [Field k]
    [AddCommGroup M] [Module (LaurentLogBase k) M] [Module.Finite (LaurentLogBase k) M] :
    Module.FinitePresentation (LaurentLogBase k) M :=
  Module.finitePresentation_of_finite (LaurentLogBase k) M

/-- In particular, each finite generated submodule appearing in the checked
finite differential filtration has an actual finite presentation. -/
theorem laurentLogBase_fg_submodule_finitePresentation (k M : Type*) [Field k]
    [AddCommGroup M] [Module (LaurentLogBase k) M]
    (P : Submodule (LaurentLogBase k) M) (hP : P.FG) :
    Module.FinitePresentation (LaurentLogBase k) P := by
  letI : Module.Finite (LaurentLogBase k) P := Module.Finite.iff_fg.mpr hP
  exact laurentLogBase_finitePresentation_of_finite k P
end StrictEUnit
#print axioms StrictEUnit.laurentLogBase_isNoetherianRing
#print axioms StrictEUnit.laurentLogBase_finitePresentation_of_finite
#print axioms StrictEUnit.laurentLogBase_fg_submodule_finitePresentation
