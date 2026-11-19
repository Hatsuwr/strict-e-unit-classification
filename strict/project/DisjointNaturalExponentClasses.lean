import IntegerClassAlignedRepresentatives
import FiniteBlockUnitAssembly

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

def exponentClassSetoid (rho : Fin r → K) : Setoid (Fin r) where
  r s t := IntegerExponentRelated (rho s) (rho t)
  iseqv := ⟨fun _ => integerExponentRelated_equivalence.refl _,
    fun h => integerExponentRelated_equivalence.symm h,
    fun h g => integerExponentRelated_equivalence.trans h g⟩

abbrev ExponentClass (rho : Fin r → K) := Quotient (exponentClassSetoid rho)
def exponentClassMap (rho : Fin r → K) (s : Fin r) : ExponentClass rho :=
  Quotient.mk _ s

/-- The class fibers partition the original indices, without duplication or omission. -/
def exponentClassPartition (rho : Fin r → K) :
    (Σ c : ExponentClass rho, {s // exponentClassMap rho s = c}) ≃ Fin r :=
  Equiv.sigmaFiberEquiv (exponentClassMap rho)

theorem exponentClassPartition_card (rho : Fin r → K) :
    Nat.card (Σ c : ExponentClass rho, {s // exponentClassMap rho s = c}) = r := by
  rw [Nat.card_congr (exponentClassPartition rho), Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A lower representative for each disjoint class makes every original shift natural.
The representatives need not themselves occur in the tuple. -/
theorem exists_disjoint_natural_exponent_classes (rho : Fin r → K) :
    ∃ xi : ExponentClass rho → K, ∃ shift : Fin r → ℕ,
      (∀ s, rho s = xi (exponentClassMap rho s) + (shift s : K)) ∧
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) := by
  classical
  let q := exponentClassMap rho
  have hr : ∀ s, IntegerExponentRelated (rho s) (rho (q s).out) := by
    intro s
    exact Quotient.exact (Quotient.out_eq (q s)).symm
  choose a ha using hr
  let B : ℕ := ∑ s, (a s).natAbs
  have hB : ∀ s, -(B : ℤ) ≤ a s := by
    intro s
    have h : (a s).natAbs ≤ B := Finset.single_le_sum (fun i _ => Nat.zero_le ((a i).natAbs)) (Finset.mem_univ s)
    have h' : ((a s).natAbs : ℤ) ≤ (B : ℤ) := by exact_mod_cast h
    have h'' := Int.natAbs_eq (a s)
    omega
  refine ⟨fun c => rho c.out - (B : K), fun s => (a s + B).toNat, ?_, ?_⟩
  · intro s
    have hn : 0 ≤ a s + (B : ℤ) := by have := hB s; omega
    have he : (((a s + B).toNat : ℕ) : K) = (a s : K) + (B : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Int.cast_add, Int.cast_natCast]
    rw [he]
    have := ha s
    dsimp [q] at *
    linear_combination this
  · intro c d hcd z hz
    apply hcd
    have hrel : IntegerExponentRelated (rho c.out) (rho d.out) := by
      refine ⟨z, ?_⟩
      linear_combination hz
    have he : (Quotient.mk (exponentClassSetoid rho) c.out) =
        Quotient.mk (exponentClassSetoid rho) d.out := Quotient.sound hrel
    simpa only [Quotient.out_eq] using he

end StrictEUnit
end
