import RankOneNoInfinity
import NoInfinityFiniteAlgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! The actual homogeneous universal inverse-pair relations and their empty
projective boundary. A basis is supplied only to express equality in A; no
finiteness of this basis or of the relation family is required. -/
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace StrictEUnit
variable {k A m n γ : Type*} [Field k] [CommRing A] [Algebra k A]
variable [Fintype m] [Fintype n]
attribute [local instance] MvPolynomial.gradedAlgebra

def universalRankOneMinor (i i' : m) (j j' : n) : MvPolynomial (Option (m × n)) k :=
  X (some (i,j)) * X (some (i',j')) - X (some (i,j')) * X (some (i',j))

def universalProductCoordinate (e : Basis γ k A) (a : m → A) (b : n → A)
    (g : γ) : MvPolynomial (Option (m × n)) k :=
  (∑ i, ∑ j, C (e.repr (a i * b j) g) * X (some (i,j))) -
    C (e.repr 1 g) * X none

def universalRankOneIdeal (e : Basis γ k A) (a : m → A) (b : n → A) :
    Ideal (MvPolynomial (Option (m × n)) k) :=
  Ideal.span (Set.range (fun q : (m × m) × (n × n) =>
    universalRankOneMinor q.1.1 q.1.2 q.2.1 q.2.2) ∪
    Set.range (universalProductCoordinate e a b))

theorem universalRankOneMinor_mem (e : Basis γ k A) (a : m → A) (b : n → A)
    (i i' : m) (j j' : n) :
    universalRankOneMinor i i' j j' ∈ universalRankOneIdeal e a b :=
  Ideal.subset_span (Or.inl ⟨((i,i'),(j,j')), rfl⟩)

theorem universalProductCoordinate_mem (e : Basis γ k A) (a : m → A) (b : n → A)
    (g : γ) : universalProductCoordinate e a b g ∈ universalRankOneIdeal e a b :=
  Ideal.subset_span (Or.inr ⟨g, rfl⟩)

theorem universalRankOneIdeal_homogeneous (e : Basis γ k A) (a : m → A) (b : n → A) :
    (universalRankOneIdeal e a b).IsHomogeneous (homogeneousSubmodule _ k) := by
  classical
  apply Ideal.homogeneous_span
  rintro p (⟨q, rfl⟩ | ⟨g, rfl⟩)
  · refine ⟨2, ?_⟩
    exact ((isHomogeneous_X k _).mul (isHomogeneous_X k _)).sub
      ((isHomogeneous_X k _).mul (isHomogeneous_X k _))
  · refine ⟨1, ?_⟩
    apply MvPolynomial.IsHomogeneous.sub
    · apply (homogeneousSubmodule _ k 1).sum_mem
      intro i hi
      apply (homogeneousSubmodule _ k 1).sum_mem
      intro j hj
      exact isHomogeneous_C_mul_X _ _
    · exact isHomogeneous_C_mul_X _ _

theorem universalRankOneIdeal_no_infinity [IsDomain A]
    (e : Basis γ k A) (a : m → A) (b : n → A)
    (ha : LinearIndependent k a) (hb : LinearIndependent k b)
    (x : Option (m × n) → k)
    (hx : ∀ f ∈ universalRankOneIdeal e a b, eval x f = 0)
    (ht : x none = 0) : ∀ ij, x (some ij) = 0 := by
  classical
  have hmin (i i' : m) (j j' : n) :
      x (some (i,j)) * x (some (i',j')) = x (some (i,j')) * x (some (i',j)) := by
    have h := hx _ (universalRankOneMinor_mem e a b i i' j j')
    simpa [universalRankOneMinor, sub_eq_zero] using h
  have hrel : ∑ i, ∑ j, x (some (i,j)) • (a i * b j) = 0 := by
    apply e.repr.injective
    ext g
    have h := hx _ (universalProductCoordinate_mem e a b g)
    simpa [universalProductCoordinate, ht, map_sum, Finsupp.sum_apply,
      Finsupp.smul_apply, mul_comm] using h
  have hz := rankOne_product_relation_zero a b ha hb (fun i j => x (some (i,j))) hmin hrel
  intro ij
  exact congrFun (congrFun hz ij.1) ij.2

theorem universalRankOneIdeal_coordinate_power [IsDomain A] [IsAlgClosed k]
    (e : Basis γ k A) (a : m → A) (b : n → A)
    (ha : LinearIndependent k a) (hb : LinearIndependent k b) (ij : m × n) :
    ∃ N : ℕ, 0 < N ∧ X (some ij) ^ N ∈
      universalRankOneIdeal e a b ⊔ Ideal.span {X none} :=
  positive_coordinate_power_of_no_infinity _
    (universalRankOneIdeal_no_infinity e a b ha hb) ij

theorem universalRankOneIdeal_finite [IsDomain A] [IsAlgClosed k]
    (e : Basis γ k A) (a : m → A) (b : n → A)
    (ha : LinearIndependent k a) (hb : LinearIndependent k b) :
    Module.Finite k (MvPolynomial (m × n) k ⧸
      Ideal.map dehomogenize.toRingHom (universalRankOneIdeal e a b)) :=
  finite_dehomogenized_quotient_of_no_infinity _
    (universalRankOneIdeal_homogeneous e a b)
    (universalRankOneIdeal_no_infinity e a b ha hb)
end StrictEUnit
#print axioms StrictEUnit.universalRankOneMinor
#print axioms StrictEUnit.universalProductCoordinate
#print axioms StrictEUnit.universalRankOneIdeal
#print axioms StrictEUnit.universalRankOneMinor_mem
#print axioms StrictEUnit.universalProductCoordinate_mem
#print axioms StrictEUnit.universalRankOneIdeal_homogeneous
#print axioms StrictEUnit.universalRankOneIdeal_no_infinity
#print axioms StrictEUnit.universalRankOneIdeal_coordinate_power
#print axioms StrictEUnit.universalRankOneIdeal_finite
