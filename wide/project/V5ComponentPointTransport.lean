import V5ComponentPoint

noncomputable section
namespace StrictEUnit
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- Algebra automorphisms carry minimal primes contravariantly to minimal primes. -/
theorem v5_minimalPrime_comap_equiv (e : R ≃ₐ[k] R) (P : Ideal R)
    (hP : P ∈ minimalPrimes R) :
    P.comap e.toRingEquiv.toRingHom ∈ minimalPrimes R := by
  letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro Q hQ hQP
  letI : Q.IsPrime := hQ.1
  have hle : Q.comap e.symm.toRingEquiv.toRingHom ≤ P := by
    intro x hx
    have hh := hQP hx
    change e (e.symm x) ∈ P at hh
    simpa only [e.apply_symm_apply] using hh
  have hrev := hP.2 ⟨inferInstance, bot_le⟩ hle
  intro x hx
  have hh := hrev hx
  change e.symm (e x) ∈ Q at hh
  simpa only [e.symm_apply_apply] using hh

/-- If a translation carries a specified point to a point on exactly one
minimal component, that specified point also lies on exactly one component. -/
theorem v5_unique_minimalPrime_transport
    (ε p : R →ₐ[k] k) (e : R ≃ₐ[k] R)
    (he : ε.comp e.toAlgHom = p)
    (P : Ideal R) (hP : P ∈ minimalPrimes R)
    (hpP : P ≤ RingHom.ker p.toRingHom)
    (hunique : ∀ Q ∈ minimalPrimes R, Q ≤ RingHom.ker p.toRingHom → Q = P) :
    ∃! Q : Ideal R, Q ∈ minimalPrimes R ∧ Q ≤ RingHom.ker ε.toRingHom := by
  have heval (x : R) : ε (e x) = p x := DFunLike.congr_fun he x
  refine ⟨P.comap e.symm.toRingEquiv.toRingHom,
    ⟨v5_minimalPrime_comap_equiv e.symm P hP, ?_⟩, ?_⟩
  · intro x hx
    have hh := hpP hx
    change p (e.symm x) = 0 at hh
    rw [← heval, e.apply_symm_apply] at hh
    exact hh
  · intro Q hQ
    have hQP : Q.comap e.toRingEquiv.toRingHom = P := by
      apply hunique _ (v5_minimalPrime_comap_equiv e Q hQ.1)
      intro x hx
      change p x = 0
      rw [← heval]
      exact hQ.2 hx
    apply Ideal.ext
    intro x
    have hh := congrArg (fun I : Ideal R => e.symm x ∈ I) hQP
    change (e (e.symm x) ∈ Q) = (e.symm x ∈ P) at hh
    change x ∈ Q ↔ e.symm x ∈ P
    exact iff_of_eq (by simpa only [e.apply_symm_apply] using hh)

/-- Point-transitivity plus finite minimal primes gives uniqueness at the
specified point. Hopf translation is an application input, not assumed as
uniqueness or as a component theorem. -/
theorem v5_unique_minimalPrime_of_point_transitive
    [IsAlgClosed k] [Algebra.FiniteType k R]
    (ε : R →ₐ[k] k) (hfinite : (minimalPrimes R).Finite)
    (htrans : ∀ p : R →ₐ[k] k, ∃ e : R ≃ₐ[k] R, ε.comp e.toAlgHom = p) :
    ∃! Q : Ideal R, Q ∈ minimalPrimes R ∧ Q ≤ RingHom.ker ε.toRingHom := by
  letI : (⊥ : Ideal k).IsPrime := Ideal.bot_prime
  letI : (RingHom.ker ε.toRingHom).IsPrime :=
    Ideal.comap_isPrime ε.toRingHom (⊥ : Ideal k)
  obtain ⟨P, hP, _⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal R)) (J := RingHom.ker ε.toRingHom) bot_le
  obtain ⟨p, hp, huniq⟩ := v5_minimal_component_unique_point (k := k) hfinite P hP
  obtain ⟨e, he⟩ := htrans p
  exact v5_unique_minimalPrime_transport ε p e he P hP hp huniq

end StrictEUnit
#print axioms StrictEUnit.v5_minimalPrime_comap_equiv
#print axioms StrictEUnit.v5_unique_minimalPrime_transport

#print axioms StrictEUnit.v5_unique_minimalPrime_of_point_transitive
