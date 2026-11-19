import AlgebraicInterfaces
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Exact kernels survive actual localization; the induced map of the
localized fiber into a domain is proved injective, rather than assumed. -/
noncomputable section
namespace StrictEUnit
variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S] [Algebra R T]

/-- A localization preserves an already proved exact specialization kernel. -/
theorem localized_specialization_kernel
    (M : Submonoid R) [IsLocalization M T]
    (ev : R →+* S) (ψ : T →+* S) (hψ : ψ.comp (algebraMap R T) = ev)
    (J : Ideal R) (hker : RingHom.ker ev = J) :
    RingHom.ker ψ = Ideal.map (algebraMap R T) J := by
  apply le_antisymm
  · intro t ht
    obtain ⟨⟨r,s⟩,hrs⟩ := IsLocalization.surj M t
    have hr : ev r = 0 := by
      have he := congrArg ψ hrs
      have hcomp : ∀ a, ψ (algebraMap R T a) = ev a := fun a => RingHom.congr_fun hψ a
      simpa only [map_mul,show ψ t = 0 from ht,zero_mul,hcomp] using he.symm
    have hrJ : r ∈ J := hker ▸ (show r ∈ RingHom.ker ev from hr)
    have hm := Ideal.mem_map_of_mem (algebraMap R T) hrJ
    rw [← hrs] at hm
    exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units T s)).mp hm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    have hr0 : ev r = 0 := show r ∈ RingHom.ker ev from hker.symm ▸ hr
    change ψ (algebraMap R T r) = 0
    rw [← RingHom.comp_apply, hψ, hr0]

/-- The map extending evaluation after inverting d, with its exact kernel. -/
theorem away_specialization_kernel (d : R) [IsLocalization.Away d T]
    (ev : R →+* S) (hd : IsUnit (ev d)) (J : Ideal R)
    (hker : RingHom.ker ev = J) :
    RingHom.ker (IsLocalization.Away.lift (S := T) d hd) = Ideal.map (algebraMap R T) J :=
  localized_specialization_kernel (Submonoid.powers d) ev _
    (IsLocalization.Away.lift_comp d hd) J hker

/-- The literal localized quotient embeds in the target, not just its image. -/
theorem away_specialization_quotient_injective (d : R) [IsLocalization.Away d T]
    (ev : R →+* S) (hd : IsUnit (ev d)) (J : Ideal R)
    (hker : RingHom.ker ev = J) :
    Function.Injective (Ideal.Quotient.lift (Ideal.map (algebraMap R T) J)
      (IsLocalization.Away.lift (S := T) d hd)
      (fun r hr => show r ∈ RingHom.ker (IsLocalization.Away.lift (S := T) d hd) from
        (away_specialization_kernel (T := T) d ev hd J hker).symm ▸ hr)) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact le_of_eq (away_specialization_kernel (T := T) d ev hd J hker)

/-- In particular, an exact numerical specialization into a domain proves
the entire localized quotient is a domain. -/
theorem away_specialization_quotient_isDomain [IsDomain S]
    (d : R) [IsLocalization.Away d T]
    (ev : R →+* S) (hd : IsUnit (ev d)) (J : Ideal R)
    (hker : RingHom.ker ev = J) : IsDomain (T ⧸ Ideal.map (algebraMap R T) J) :=
  Function.Injective.isDomain _ (away_specialization_quotient_injective (T := T) d ev hd J hker)
end StrictEUnit
#print axioms StrictEUnit.localized_specialization_kernel
#print axioms StrictEUnit.away_specialization_kernel
#print axioms StrictEUnit.away_specialization_quotient_injective
#print axioms StrictEUnit.away_specialization_quotient_isDomain
