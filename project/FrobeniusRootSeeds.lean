import PolynomialDifferentialOperator
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Fintype.BigOperators

/-!
# Repeated indicial roots and their polynomial seeds

The index is exactly one copy of `Fin (P.rootMultiplicity rho)` for each root
of P in K. Its cardinality is the root multiset cardinality without additional
assumptions, and is P.natDegree when P splits over K. An order r conclusion
requires the separate equality P.natDegree = r, never merely P != 0.

In characteristic zero the seed X^j lies in the kernel of the literal
P(D+rho). This is only a finite index/count and seed-kernel module, not a
Frobenius basis or a completeness assertion. No algebraic closure, rational
spectrum, or nonzero-degree assumption is imposed.

SOURCE-ONLY DRAFT: not compiler checked or independently exported.
-/

noncomputable section
open Polynomial
open scoped BigOperators Classical

namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Roots in K, each repeated exactly according to its multiplicity in P. -/
def frobeniusRootSeedIndex (P : Polynomial K) : Type _ :=
  Σ rho : {x : K // x ∈ P.roots.toFinset}, Fin (P.rootMultiplicity rho.1)

instance frobeniusRootSeedIndexFintype (P : Polynomial K) :
    Fintype (frobeniusRootSeedIndex P) := by
  unfold frobeniusRootSeedIndex
  infer_instance

def frobeniusRootSeedExponent (P : Polynomial K) (i : frobeniusRootSeedIndex P) : K :=
  i.1.1

def frobeniusRootSeedOrder (P : Polynomial K) (i : frobeniusRootSeedIndex P) : ℕ :=
  i.2.1

def frobeniusRootSeedPolynomial (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) : Polynomial K :=
  Polynomial.X ^ frobeniusRootSeedOrder P i

theorem frobeniusRootSeedExponent_mem_roots (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) : frobeniusRootSeedExponent P i ∈ P.roots :=
  Multiset.mem_toFinset.mp i.1.2

theorem frobeniusRootSeedExponent_isRoot (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) : P.IsRoot (frobeniusRootSeedExponent P i) :=
  Polynomial.isRoot_of_mem_roots (frobeniusRootSeedExponent_mem_roots P i)

/-- The existence of a seed index excludes the zero polynomial. -/
theorem frobeniusRootSeedIndex_ne_zero (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) : P ≠ 0 :=
  Polynomial.ne_zero_of_mem_roots (frobeniusRootSeedExponent_mem_roots P i)

theorem frobeniusRootSeedOrder_lt (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) :
    frobeniusRootSeedOrder P i < P.rootMultiplicity (frobeniusRootSeedExponent P i) :=
  i.2.isLt

/-- The finite sigma count is exactly the sum of root multiplicities. -/
theorem frobeniusRootSeedIndex_card_sum (P : Polynomial K) :
    Fintype.card (frobeniusRootSeedIndex P) =
      ∑ rho ∈ P.roots.toFinset, P.rootMultiplicity rho := by
  simp only [frobeniusRootSeedIndex, Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_coe_sort P.roots.toFinset (fun rho => P.rootMultiplicity rho)

/-- No splitting or nonzero assumption is needed for the root multiset count. -/
theorem frobeniusRootSeedIndex_card_roots (P : Polynomial K) :
    Fintype.card (frobeniusRootSeedIndex P) = P.roots.card := by
  rw [frobeniusRootSeedIndex_card_sum]
  simpa only [Polynomial.count_roots] using Multiset.toFinset_sum_count_eq P.roots

theorem frobeniusRootSeedIndex_card_le_natDegree (P : Polynomial K) :
    Fintype.card (frobeniusRootSeedIndex P) ≤ P.natDegree := by
  rw [frobeniusRootSeedIndex_card_roots]
  exact Polynomial.card_roots' P

/-- This includes zero and constant symbols: both counts are then zero. -/
theorem frobeniusRootSeedIndex_card_natDegree (P : Polynomial K)
    (hP : P.Splits (RingHom.id K)) :
    Fintype.card (frobeniusRootSeedIndex P) = P.natDegree :=
  (frobeniusRootSeedIndex_card_roots P).trans (Polynomial.splits_iff_card_roots.mp hP)

/-- Full order is an explicit hypothesis, separate from symbol nonvanishing. -/
theorem frobeniusRootSeedIndex_card_order (P : Polynomial K)
    (hP : P.Splits (RingHom.id K)) (r : ℕ) (hr : P.natDegree = r) :
    Fintype.card (frobeniusRootSeedIndex P) = r :=
  (frobeniusRootSeedIndex_card_natDegree P hP).trans hr

@[simp] theorem frobeniusRootSeedIndex_card_zero :
    Fintype.card (frobeniusRootSeedIndex (0 : Polynomial K)) = 0 := by
  rw [frobeniusRootSeedIndex_card_roots, Polynomial.roots_zero]
  rfl

@[simp] theorem frobeniusRootSeedIndex_card_C (c : K) :
    Fintype.card (frobeniusRootSeedIndex (Polynomial.C c)) = 0 := by
  rw [frobeniusRootSeedIndex_card_roots, Polynomial.roots_C]
  rfl

theorem frobeniusRootSeedIndex_card_eq_zero_of_natDegree_eq_zero (P : Polynomial K)
    (hP : P.natDegree = 0) : Fintype.card (frobeniusRootSeedIndex P) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [hP] using frobeniusRootSeedIndex_card_le_natDegree P

/-- The root and logarithmic order together recover the complete index. -/
theorem frobeniusRootSeedIndex_ext (P : Polynomial K)
    {i j : frobeniusRootSeedIndex P}
    (hroot : frobeniusRootSeedExponent P i = frobeniusRootSeedExponent P j)
    (horder : frobeniusRootSeedOrder P i = frobeniusRootSeedOrder P j) : i = j := by
  rcases i with ⟨⟨rho, hrho⟩, i⟩
  rcases j with ⟨⟨sigma, hsigma⟩, j⟩
  change rho = sigma at hroot
  subst sigma
  have hij : i = j := Fin.ext horder
  subst j
  rfl

theorem frobeniusRootSeedIndex_pair_injective (P : Polynomial K) :
    Function.Injective (fun i : frobeniusRootSeedIndex P =>
      (frobeniusRootSeedExponent P i, frobeniusRootSeedOrder P i)) := by
  intro i j h
  exact frobeniusRootSeedIndex_ext P (congrArg Prod.fst h) (congrArg Prod.snd h)

@[simp] theorem frobeniusRootSeedPolynomial_natDegree (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) :
    (frobeniusRootSeedPolynomial P i).natDegree = frobeniusRootSeedOrder P i := by
  exact Polynomial.natDegree_X_pow _

/-- Seeds for different roots can coincide, so the exponent remains in the pair. -/
theorem frobeniusRootSeedIndex_polynomial_pair_injective (P : Polynomial K) :
    Function.Injective (fun i : frobeniusRootSeedIndex P =>
      (frobeniusRootSeedExponent P i, frobeniusRootSeedPolynomial P i)) := by
  intro i j h
  apply frobeniusRootSeedIndex_ext P (congrArg Prod.fst h)
  have hp := congrArg (fun p : K × Polynomial K => p.2.natDegree) h
  simpa only [frobeniusRootSeedPolynomial_natDegree] using hp

section CharZero
variable [CharZero K]

/-- Every power below the exact root multiplicity is killed by literal P(D+rho). -/
theorem shiftedPolynomialDifferentialOperator_X_pow_eq_zero (P : Polynomial K)
    (rho : K) (hP : P ≠ 0) (j : Fin (P.rootMultiplicity rho)) :
    shiftedPolynomialDifferentialOperator rho P (Polynomial.X ^ j.val) = 0 := by
  apply (shiftedPolynomialDifferentialOperator_kernel_iff rho P _ hP).mpr
  rw [Polynomial.degree_X_pow]
  exact WithBot.coe_lt_coe.mpr j.isLt

/-- The zero-symbol case is vacuous because the index carries a genuine root. -/
theorem frobeniusRootSeedPolynomial_mem_kernel (P : Polynomial K)
    (i : frobeniusRootSeedIndex P) :
    shiftedPolynomialDifferentialOperator (frobeniusRootSeedExponent P i) P
      (frobeniusRootSeedPolynomial P i) = 0 :=
  shiftedPolynomialDifferentialOperator_X_pow_eq_zero P
    (frobeniusRootSeedExponent P i) (frobeniusRootSeedIndex_ne_zero P i) i.2

end CharZero
end StrictEUnit
