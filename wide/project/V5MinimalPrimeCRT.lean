import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Algebra.Pi

noncomputable section
namespace StrictEUnit
variable {k H : Type*} [CommSemiring k] [CommRing H] [Algebra k H]

/-- Canonical algebra map to the product of a family of ideal quotients. -/
def v5IdealProductMap {ι : Type*} (I : ι → Ideal H) : H →ₐ[k] (∀ i, H ⧸ I i) :=
  Pi.algHom k (fun i => H ⧸ I i) (fun i => Ideal.Quotient.mkₐ k (I i))

/-- Chinese remainder theorem as a k-algebra equivalence when the ideal
intersection is zero. This theorem does not assume reducedness implicitly. -/
def v5ZeroIntersectionCRT {ι : Type*} [Finite ι] (I : ι → Ideal H)
    (hcop : Pairwise (fun i j => IsCoprime (I i) (I j)))
    (hinf : (⨅ i, I i) = ⊥) : H ≃ₐ[k] (∀ i, H ⧸ I i) := by
  refine AlgEquiv.ofBijective (v5IdealProductMap (k := k) I) ⟨?_, ?_⟩
  · intro x y hxy
    have hd : x - y ∈ ⨅ i, I i := by
      rw [Ideal.mem_iInf]
      intro i
      exact Ideal.Quotient.eq.mp (congrFun hxy i)
    rw [hinf] at hd
    exact sub_eq_zero.mp (Ideal.mem_bot.mp hd)
  · intro y
    obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective hcop y
    exact ⟨x, funext hx⟩

@[simp] theorem v5ZeroIntersectionCRT_apply {ι : Type*} [Finite ι] (I : ι → Ideal H)
    (hcop : Pairwise (fun i j => IsCoprime (I i) (I j)))
    (hinf : (⨅ i, I i) = ⊥) (h : H) (i : ι) :
    v5ZeroIntersectionCRT (k := k) I hcop hinf h i = Ideal.Quotient.mk (I i) h := rfl

/-- In a reduced ring, the intersection of its minimal primes is zero. -/
theorem v5_reduced_iInf_minimalPrimes [IsReduced H] :
    (⨅ P : minimalPrimes H, (P : Ideal H)) = ⊥ := by
  rw [← sInf_eq_iInf']
  change sInf (⊥ : Ideal H).minimalPrimes = ⊥
  rw [Ideal.sInf_minimalPrimes]
  exact (nilradical_eq_bot_iff (R := H)).mpr inferInstance

/-- A reduced algebra with finitely many pairwise comaximal minimal primes
is the product of its actual minimal-prime quotient algebras. -/
def v5MinimalPrimeCRT [IsReduced H] [Finite (minimalPrimes H)]
    (hcop : Pairwise (fun P Q : minimalPrimes H => IsCoprime (P : Ideal H) (Q : Ideal H))) :
    H ≃ₐ[k] (∀ P : minimalPrimes H, H ⧸ (P : Ideal H)) :=
  v5ZeroIntersectionCRT (k := k) (fun P : minimalPrimes H => (P : Ideal H))
    hcop v5_reduced_iInf_minimalPrimes

@[simp] theorem v5MinimalPrimeCRT_apply [IsReduced H] [Finite (minimalPrimes H)]
    (hcop : Pairwise (fun P Q : minimalPrimes H => IsCoprime (P : Ideal H) (Q : Ideal H)))
    (h : H) (P : minimalPrimes H) :
    v5MinimalPrimeCRT (k := k) hcop h P = Ideal.Quotient.mk (P : Ideal H) h := rfl

end StrictEUnit
#print axioms StrictEUnit.v5ZeroIntersectionCRT
#print axioms StrictEUnit.v5ZeroIntersectionCRT_apply
#print axioms StrictEUnit.v5_reduced_iInf_minimalPrimes
#print axioms StrictEUnit.v5MinimalPrimeCRT
#print axioms StrictEUnit.v5MinimalPrimeCRT_apply
