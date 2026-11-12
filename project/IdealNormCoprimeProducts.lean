import IdealNormDirichletBound

noncomputable section
open scoped NumberField Topology nonZeroDivisors BigOperators
open NumberField Finset
namespace StrictEUnit

theorem ideals_isCoprime_of_absNorm_coprime
    (K : Type*) [Field K] [NumberField K] {I J : Ideal (𝓞 K)}
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff]
  apply Ideal.absNorm_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes h
    (Ideal.absNorm_dvd_absNorm_of_le le_sup_left)
    (Ideal.absNorm_dvd_absNorm_of_le le_sup_right)

theorem idealNormFiber_mul_injective
    (K : Type*) [Field K] [NumberField K] {m n : ℕ} (h : m.Coprime n) :
    Function.Injective (fun x :
      {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = m} ×
      {J : (Ideal (𝓞 K))⁰ | Ideal.absNorm (J : Ideal (𝓞 K)) = n} => x.1.val * x.2.val) := by
  rintro ⟨I,J⟩ ⟨I',J'⟩ he
  change I.val * J.val = I'.val * J'.val at he
  have he' : (I.val : Ideal (𝓞 K)) * (J.val : Ideal (𝓞 K)) =
      (I'.val : Ideal (𝓞 K)) * (J'.val : Ideal (𝓞 K)) := congrArg Subtype.val he
  have hc : IsCoprime (I.val : Ideal (𝓞 K)) (J'.val : Ideal (𝓞 K)) :=
    ideals_isCoprime_of_absNorm_coprime K (by
      change (Ideal.absNorm (I.val : Ideal (𝓞 K))).Coprime (Ideal.absNorm (J'.val : Ideal (𝓞 K)))
      rw [show Ideal.absNorm (I.val : Ideal (𝓞 K)) = m from I.prop,
        show Ideal.absNorm (J'.val : Ideal (𝓞 K)) = n from J'.prop]
      exact h)
  have hc' : IsCoprime (I'.val : Ideal (𝓞 K)) (J.val : Ideal (𝓞 K)) :=
    ideals_isCoprime_of_absNorm_coprime K (by
      change (Ideal.absNorm (I'.val : Ideal (𝓞 K))).Coprime (Ideal.absNorm (J.val : Ideal (𝓞 K)))
      rw [show Ideal.absNorm (I'.val : Ideal (𝓞 K)) = m from I'.prop,
        show Ideal.absNorm (J.val : Ideal (𝓞 K)) = n from J.prop]
      exact h)
  have hi : (I.val : Ideal (𝓞 K)) = (I'.val : Ideal (𝓞 K)) := by
    apply le_antisymm
    · exact Ideal.dvd_iff_le.mp (hc'.dvd_of_dvd_mul_right (he' ▸ dvd_mul_right _ _))
    · exact Ideal.dvd_iff_le.mp (hc.dvd_of_dvd_mul_right (he'.symm ▸ dvd_mul_right _ _))
  have hi' : I.val = I'.val := Subtype.ext hi
  have hj' : J.val = J'.val := mul_left_cancel (hi' ▸ he)
  exact Prod.ext (Subtype.ext hi') (Subtype.ext hj')

/-- A sufficient direction for Euler-product lower bounds: products of ideals
of coprime norms give distinct ideals of product norm. -/
theorem idealNormCoefficient_coprime_supermultiplicative
    (K : Type*) [Field K] [NumberField K] {m n : ℕ} (h : m.Coprime n) :
    idealNormCoefficient K m * idealNormCoefficient K n ≤ idealNormCoefficient K (m*n) := by
  letI := finite_idealNorm_fiber K (m*n)
  let f : ({I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = m} ×
      {J : (Ideal (𝓞 K))⁰ | Ideal.absNorm (J : Ideal (𝓞 K)) = n}) →
      {A : (Ideal (𝓞 K))⁰ | Ideal.absNorm (A : Ideal (𝓞 K)) = m*n} :=
    fun x => ⟨x.1.val*x.2.val, by change Ideal.absNorm (_ * _) = _; rw [map_mul, x.1.prop, x.2.prop]⟩
  have hf : Function.Injective f := fun x y he =>
    idealNormFiber_mul_injective K h (congrArg Subtype.val he)
  simpa only [Nat.card_prod, idealNormCoefficient] using Nat.card_le_card_of_injective f hf

end StrictEUnit
end
