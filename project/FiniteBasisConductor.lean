import KummerResidueCertificate

noncomputable section
namespace StrictEUnit

/-- Finitely many basis denominators clear the entire order at once. -/
theorem exists_integer_conductor_of_basis_clearings
    {R S ι : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Fintype ι]
    (b : Basis ι R S) (a : S)
    (h : ∀ i, ∃ d : R, d ≠ 0 ∧ d • b i ∈ Algebra.adjoin R {a}) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R S d ∈ conductor R a := by
  classical
  choose d hd hm using h
  let D : R := ∏ i, d i
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have hb : ∀ i, D • b i ∈ Algebra.adjoin R {a} := by
    intro i
    have he : D = (∏ j ∈ Finset.univ.erase i, d j) * d i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [he, mul_smul]
    exact (Algebra.adjoin R {a}).toSubmodule.smul_mem (∏ j ∈ Finset.univ.erase i, d j) (hm i)
  refine ⟨D, hD, mem_conductor_iff.mpr ?_⟩
  intro x
  rw [← Algebra.smul_def]
  rw [← b.sum_repr x, Finset.smul_sum]
  apply (Algebra.adjoin R {a}).toSubmodule.sum_mem
  intro i _
  rw [smul_comm]
  exact (Algebra.adjoin R {a}).toSubmodule.smul_mem (b.repr x i) (hb i)

/-- A conductor integer avoids every maximal ideal not containing it. -/
theorem conductor_coprime_of_integer_not_mem
    {S : Type*} [CommRing S] [Algebra ℤ S] (a : S)
    (d : ℤ) (hd : algebraMap ℤ S d ∈ conductor ℤ a)
    (I : Ideal ℤ) [hI : I.IsMaximal] (hnot : d ∉ I) :
    (conductor ℤ a).comap (algebraMap ℤ S) ⊔ I = ⊤ := by
  by_contra hn
  have he := hI.eq_of_le hn
    (show I ≤ (conductor ℤ a).comap (algebraMap ℤ S) ⊔ I from le_sup_right)
  apply hnot
  rw [he]
  exact (show (conductor ℤ a).comap (algebraMap ℤ S) ≤
    (conductor ℤ a).comap (algebraMap ℤ S) ⊔ I from le_sup_left) hd

end StrictEUnit
end
