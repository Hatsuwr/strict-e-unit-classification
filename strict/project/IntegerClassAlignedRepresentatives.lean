import AlignedClassPivotNonvanishing
import IntegerClassSeparation

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Every finite exponent tuple can be aligned by individual integer shifts.
Representatives are selected from the same tuple, not new field elements. -/
theorem exists_integerClass_aligned_representatives {r : ℕ} (rho : Fin r → K) :
    ∃ rep : Fin r → Fin r,∃ shift : Fin r → ℤ,
      (∀ s,rho s=rho (rep s)+(shift s : K)) ∧
      (∀ s t,rho (rep s)=rho (rep t) ∨
        ∀ z : ℤ,rho (rep s)-rho (rep t)≠(z : K)) := by
  classical
  let st : Setoid (Fin r) :=
    { r := fun s t => IntegerExponentRelated (rho s) (rho t)
      iseqv := ⟨fun s => integerExponentRelated_equivalence.refl _,
        fun h => integerExponentRelated_equivalence.symm h,
        fun h g => integerExponentRelated_equivalence.trans h g⟩ }
  let q : Fin r → Quotient st := fun s => Quotient.mk st s
  let rep : Fin r → Fin r := fun s => (q s).out
  have hr : ∀ s,IntegerExponentRelated (rho s) (rho (rep s)) := by
    intro s
    exact Quotient.exact (Quotient.out_eq (q s)).symm
  choose shift hs using hr
  refine ⟨rep,shift,?_,?_⟩
  · intro s
    have h := hs s
    linear_combination h
  · intro s t
    by_cases he : q s=q t
    · left
      change rho ((q s).out)=rho ((q t).out)
      rw [he]
    · right
      intro z hz
      apply he
      have hre : q (rep s)=q (rep t) := Quotient.sound ⟨z,hz⟩
      have h1 : q (rep s)=q s := Quotient.out_eq (q s)
      have h2 : q (rep t)=q t := Quotient.out_eq (q t)
      exact h1.symm.trans (hre.trans h2)

end StrictEUnit
end
