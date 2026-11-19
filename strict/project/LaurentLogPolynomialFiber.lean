import PolynomialRelationFiber

/-! Exact relation lifting for the manuscript parameters t,t inverse,ell,
z=t^N. The generators may satisfy arbitrary relations. -/
noncomputable section
namespace StrictEUnit
variable {k R S ι : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

def laurentLogFiberIdeal (t : Rˣ) (ell : R) : Ideal R :=
  Ideal.span {(t:R)-1, ell}

def laurentLogFiberParameters (t : Rˣ) (ell : R) : Option Bool → R
  | none => t
  | some false => ↑(t⁻¹)
  | some true => ell

theorem laurentLogFiberParameter_reduction (t : Rˣ) (ell : R) :
    ∀ s, ∃ a : k, laurentLogFiberParameters t ell s - algebraMap k R a ∈
      laurentLogFiberIdeal t ell := by
  let J := laurentLogFiberIdeal t ell
  have ht : (t:R)-1 ∈ J := Ideal.subset_span (by simp)
  have hl : ell ∈ J := Ideal.subset_span (by simp)
  have htq : Ideal.Quotient.mk J (t:R) = 1 := by
    simpa using (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ht
  have hiq : Ideal.Quotient.mk J (↑(t⁻¹):R) = 1 := by
    have h := congrArg (Ideal.Quotient.mk J) (show (t:R) * (↑(t⁻¹):R) = 1 by simp)
    simpa only [map_mul,map_one,htq,one_mul] using h
  intro s
  cases s with
  | none => exact ⟨1,by simpa [laurentLogFiberParameters] using ht⟩
  | some b =>
    cases b with
    | false => exact ⟨1,by
        simpa [laurentLogFiberParameters] using
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem (↑(t⁻¹):R) 1).mp (by simpa using hiq)⟩
    | true => exact ⟨0,by simpa [laurentLogFiberParameters] using hl⟩

theorem laurentLogFiber_power_sub_one (t : Rˣ) (ell : R) (N : ℕ) :
    (t:R)^N-1 ∈ laurentLogFiberIdeal t ell := by
  let J := laurentLogFiberIdeal t ell
  have ht : (t:R)-1 ∈ J := Ideal.subset_span (by simp)
  have htq : Ideal.Quotient.mk J (t:R) = 1 := by
    simpa using (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ht
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  change Ideal.Quotient.mk J ((t:R)^N) = Ideal.Quotient.mk J 1
  simp only [map_pow,htq,one_pow,map_one]

theorem laurentLogFiberIdeal_le_kernel
    (ev : R →ₐ[k] S) (t : Rˣ) (ell : R)
    (ht : ev (t:R) = 1) (hl : ev ell = 0) :
    laurentLogFiberIdeal t ell ≤ RingHom.ker ev.toRingHom := by
  apply Ideal.span_le.mpr
  intro r hr
  rcases hr with rfl | hr
  · change ev ((t:R)-1) = 0
    simp [ht]
  · have he : r = ell := Set.mem_singleton_iff.mp hr
    subst r
    exact hl

/-- The algebraic section-8 conclusion. Only the explicit Beukers polynomial
lift remains an external mathematical premise. -/
theorem laurentLogFiber_kernel_of_polynomial_lifts
    (ev : R →ₐ[k] S) (t : Rˣ) (ell : R) (F : ι → R) (N : ℕ)
    (hgen : Algebra.adjoin k
      (Set.range F ∪ Set.range (laurentLogFiberParameters t ell)) = ⊤)
    (ht : ev (t:R) = 1) (hl : ev ell = 0)
    (hlift : ∀ P : MvPolynomial ι k, ev (MvPolynomial.aeval F P) = 0 →
      ∃ Q : Polynomial (MvPolynomial ι k),
        Polynomial.eval₂ (MvPolynomial.aeval F).toRingHom ((t:R)^N) Q = 0 ∧
          Q.eval 1 = P) :
    RingHom.ker ev.toRingHom = laurentLogFiberIdeal t ell :=
  kernel_eq_of_generated_polynomial_lifts ev F (laurentLogFiberParameters t ell)
    ((t:R)^N) (laurentLogFiberIdeal t ell) hgen
    (laurentLogFiberParameter_reduction t ell)
    (laurentLogFiberIdeal_le_kernel ev t ell ht hl)
    (laurentLogFiber_power_sub_one t ell N) hlift
end StrictEUnit
#print axioms StrictEUnit.laurentLogFiberIdeal
#print axioms StrictEUnit.laurentLogFiberParameters
#print axioms StrictEUnit.laurentLogFiberParameter_reduction
#print axioms StrictEUnit.laurentLogFiber_power_sub_one
#print axioms StrictEUnit.laurentLogFiberIdeal_le_kernel
#print axioms StrictEUnit.laurentLogFiber_kernel_of_polynomial_lifts
