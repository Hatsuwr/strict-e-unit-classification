import Mathlib.RingTheory.Polynomial.GaussLemma

/-! New reconstruction, not recovered historical source.
Monic factors descend through a relatively algebraically closed field extension.
This supplies a genuine algebraic prerequisite, without asserting the tensor
product or analytic closure conclusions. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

namespace StrictEUnit
open Polynomial

/-- Every monic factor of a polynomial over the smaller field descends. -/
theorem relative_closed_monic_factor_descends
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsIntegrallyClosedIn F E]
    {p : F[X]} (hp : p.Monic) {q : E[X]} (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap F E)) :
    ∃ q₀ : F[X], q₀.map (algebraMap F E) = q := by
  apply (Polynomial.mem_lifts q).mp
  apply (Polynomial.lifts_iff_coeff_lifts q).mpr
  intro n
  have hq' := integralClosure.mem_lifts_of_monic_of_dvd_map E hp hq hd
  obtain ⟨c, hc⟩ := (Polynomial.lifts_iff_coeff_lifts q).mp hq' n
  apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
  rw [← hc]
  exact c.property

/-- A monic irreducible polynomial stays irreducible over a relatively
algebraically closed extension. -/
theorem relative_closed_monic_irreducible_map
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsIntegrallyClosedIn F E]
    {p : F[X]} (hp : p.Monic) (hi : Irreducible p) :
    Irreducible (p.map (algebraMap F E)) := by
  have hinj := Polynomial.map_injective (algebraMap F E)
    (algebraMap F E).injective
  have hp1 : p ≠ 1 := by
    intro h
    apply hi.not_isUnit
    rw [h]
    exact isUnit_one
  have hpmap1 : p.map (algebraMap F E) ≠ 1 := by
    intro h
    apply hp1
    apply hinj
    simpa only [Polynomial.map_one] using h
  apply (Polynomial.irreducible_of_monic (hp.map _) hpmap1).mpr
  intro a b ha hb hab
  obtain ⟨a₀, ha₀⟩ := relative_closed_monic_factor_descends hp ha
    (dvd_of_mul_right_eq b hab)
  obtain ⟨b₀, hb₀⟩ := relative_closed_monic_factor_descends hp hb
    (dvd_of_mul_left_eq a hab)
  have hab₀ : p = a₀ * b₀ := by
    apply hinj
    rw [Polynomial.map_mul, ha₀, hb₀]
    exact hab.symm
  rcases hi.isUnit_or_isUnit hab₀ with hu | hu
  · left
    apply ha.eq_one_of_isUnit
    rw [← ha₀]
    exact hu.map (Polynomial.mapRingHom (algebraMap F E))
  · right
    apply hb.eq_one_of_isUnit
    rw [← hb₀]
    exact hu.map (Polynomial.mapRingHom (algebraMap F E))

end StrictEUnit
