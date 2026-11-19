import V5ComponentPointTransport

noncomputable section
namespace StrictEUnit
variable {k R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.FiniteType k R]

omit [IsAlgClosed k] [Algebra.FiniteType k R] in
/-- Uniqueness at one point propagates along algebra automorphisms. -/
theorem v5_unique_minimalPrime_at_every_point
    (ε : R →ₐ[k] k)
    (hε : ∃! P : Ideal R, P ∈ minimalPrimes R ∧ P ≤ RingHom.ker ε.toRingHom)
    (htrans : ∀ p : R →ₐ[k] k, ∃ e : R ≃ₐ[k] R, ε.comp e.toAlgHom = p)
    (p : R →ₐ[k] k) :
    ∃! P : Ideal R, P ∈ minimalPrimes R ∧ P ≤ RingHom.ker p.toRingHom := by
  obtain ⟨P, hP, huniq⟩ := hε
  obtain ⟨e, he⟩ := htrans p
  have hinv : p.comp e.symm.toAlgHom = ε := by
    ext x
    have hh := DFunLike.congr_fun he (e.symm x)
    change ε (e (e.symm x)) = p (e.symm x) at hh
    change p (e.symm x) = ε x
    simpa only [e.apply_symm_apply] using hh.symm
  exact v5_unique_minimalPrime_transport p ε e.symm hinv P hP.1 hP.2
    (fun Q hQ hle => huniq Q ⟨hQ, hle⟩)

/-- If every rational point lies on exactly one minimal component, distinct
minimal primes are comaximal. The common point of a hypothetical proper sum
is obtained from a maximal ideal and the weak Nullstellensatz. -/
theorem v5_minimalPrimes_pairwise_comaximal
    (hpoints : ∀ p : R →ₐ[k] k,
      ∃! P : Ideal R, P ∈ minimalPrimes R ∧ P ≤ RingHom.ker p.toRingHom)
    (P Q : Ideal R) (hP : P ∈ minimalPrimes R) (hQ : Q ∈ minimalPrimes R)
    (hne : P ≠ Q) : P ⊔ Q = ⊤ := by
  by_contra hproper
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (P ⊔ Q) hproper
  letI : M.IsMaximal := hM
  let p : R →ₐ[k] k := maximalIdealPoint (k := k) M
  have hp : RingHom.ker p.toRingHom = M := maximalIdealPoint_ker (k := k) M
  obtain ⟨J, _, huniq⟩ := hpoints p
  have hPJ : P = J := huniq P ⟨hP, by rw [hp]; exact le_trans le_sup_left hle⟩
  have hQJ : Q = J := huniq Q ⟨hQ, by rw [hp]; exact le_trans le_sup_right hle⟩
  exact hne (hPJ.trans hQJ.symm)

/-- The point-transitive application; only uniqueness at the distinguished
point is needed, not finiteness or reducedness as additional hypotheses. -/
theorem v5_minimalPrimes_pairwise_comaximal_of_point_transitive
    (ε : R →ₐ[k] k)
    (hε : ∃! P : Ideal R, P ∈ minimalPrimes R ∧ P ≤ RingHom.ker ε.toRingHom)
    (htrans : ∀ p : R →ₐ[k] k, ∃ e : R ≃ₐ[k] R, ε.comp e.toAlgHom = p)
    (P Q : Ideal R) (hP : P ∈ minimalPrimes R) (hQ : Q ∈ minimalPrimes R)
    (hne : P ≠ Q) : P ⊔ Q = ⊤ :=
  v5_minimalPrimes_pairwise_comaximal
    (v5_unique_minimalPrime_at_every_point ε hε htrans) P Q hP hQ hne

end StrictEUnit
#print axioms StrictEUnit.v5_unique_minimalPrime_at_every_point
#print axioms StrictEUnit.v5_minimalPrimes_pairwise_comaximal
#print axioms StrictEUnit.v5_minimalPrimes_pairwise_comaximal_of_point_transitive
