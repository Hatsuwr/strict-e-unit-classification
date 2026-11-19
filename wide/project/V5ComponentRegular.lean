import V5HopfTranslation
import V5ComponentPointTransport
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Translation sends the selected minimal component to the identity component. -/
theorem v5ComponentTranslate_ideal
    (ε p : H →ₐ[k] k) (e : H ≃ₐ[k] H) (he : ε.comp e.toAlgHom = p)
    (P I : Ideal H) (hP : P ∈ minimalPrimes H)
    (hp : P ≤ RingHom.ker p.toRingHom)
    (hu : ∀ Q ∈ minimalPrimes H, Q ≤ RingHom.ker ε.toRingHom → Q = I) :
    I = P.map e.toRingEquiv.toRingHom := by
  have hQ := v5_minimalPrime_comap_equiv e.symm P hP
  have hle : P.comap e.symm.toRingEquiv.toRingHom ≤ RingHom.ker ε.toRingHom := by
    intro x hx
    have hh := hp hx
    have heval := DFunLike.congr_fun he (e.symm x)
    change ε (e (e.symm x)) = p (e.symm x) at heval
    change ε x = 0
    simpa only [e.apply_symm_apply] using heval.trans hh
  rw [← hu _ hQ hle]
  exact (Ideal.map_comap_of_equiv e.toRingEquiv).symm

/-- The resulting algebra equivalence of the selected and identity components. -/
def v5ComponentTranslateEquiv
    (ε p : H →ₐ[k] k) (e : H ≃ₐ[k] H) (he : ε.comp e.toAlgHom = p)
    (P I : Ideal H) (hP : P ∈ minimalPrimes H)
    (hp : P ≤ RingHom.ker p.toRingHom)
    (hu : ∀ Q ∈ minimalPrimes H, Q ≤ RingHom.ker ε.toRingHom → Q = I) :
    (H ⧸ P) ≃ₐ[k] (H ⧸ I) :=
  Ideal.quotientEquivAlg P I e (v5ComponentTranslate_ideal ε p e he P I hP hp hu)

/-- Specialization to genuine Hopf translation; only a point on P is needed. -/
def v5HopfComponentEquiv
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)
    (p : H →ₐ[k] k) (P I : Ideal H) (hP : P ∈ minimalPrimes H)
    (hp : P ≤ RingHom.ker p.toRingHom)
    (hu : ∀ Q ∈ minimalPrimes H,
      Q ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → Q = I) :
    (H ⧸ P) ≃ₐ[k] (H ⧸ I) :=
  v5ComponentTranslateEquiv (Bialgebra.counitAlgHom k H) p
    (v5HopfTranslation s hs p) (v5HopfTranslation_at_counit s hs p) P I hP hp hu

theorem v5HopfComponentEquiv_mk
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)
    (p : H →ₐ[k] k) (P I : Ideal H) (hP : P ∈ minimalPrimes H)
    (hp : P ≤ RingHom.ker p.toRingHom)
    (hu : ∀ Q ∈ minimalPrimes H,
      Q ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → Q = I) (x : H) :
    v5HopfComponentEquiv s hs p P I hP hp hu (Ideal.Quotient.mk P x) =
      Ideal.Quotient.mk I (v5HopfTranslate p x) := rfl

theorem v5HopfTranslate_comul (p : H →ₐ[k] k) (x : H) :
    Bialgebra.comulAlgHom k H (v5HopfTranslate p x) =
      Algebra.TensorProduct.map (v5HopfTranslate p) (AlgHom.id k H)
        (Bialgebra.comulAlgHom k H x) := by
  let a : H →ₐ[k] H ⊗[k] H := (Algebra.ofId k (H ⊗[k] H)).comp p
  let l : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeLeft (R := k) (A := H) (B := H)
  let r := Algebra.TensorProduct.includeRight (R := k) (A := H) (B := H)
  have hlr : v5HopfConv l r = Bialgebra.comulAlgHom k H := by
    have h : Algebra.TensorProduct.lift l r (fun _ _ => .all _ _) = AlgHom.id k (H ⊗[k] H) := by
      apply AlgHom.toLinearMap_injective
      ext y z
      simp [l, r]
    change (Algebra.TensorProduct.lift l r _).comp _ = _
    rw [h, AlgHom.id_comp]
  have hal : v5HopfConv a l = l.comp (v5HopfTranslate p) := by
    rw [v5HopfTranslate, v5HopfConv_comp]
    congr 1
  have hd : (Bialgebra.comulAlgHom k H).comp (v5HopfTranslate p) =
      v5HopfConv a (Bialgebra.comulAlgHom k H) := by
    rw [v5HopfTranslate, v5HopfConv_comp, AlgHom.comp_id]
    congr 1
    ext y
    exact (Bialgebra.comulAlgHom k H).commutes (p y)
  have hm : (Algebra.TensorProduct.map (v5HopfTranslate p) (AlgHom.id k H)).comp
      (Bialgebra.comulAlgHom k H) = v5HopfConv (l.comp (v5HopfTranslate p)) r := by
    have h : Algebra.TensorProduct.map (v5HopfTranslate p) (AlgHom.id k H) =
        Algebra.TensorProduct.lift (l.comp (v5HopfTranslate p)) r (fun _ _ => .all _ _) := by
      apply AlgHom.toLinearMap_injective
      ext y z
      simp [l, r]
    change _ = (Algebra.TensorProduct.lift _ _ _).comp _
    rw [h]
  change ((Bialgebra.comulAlgHom k H).comp (v5HopfTranslate p)) x = _
  rw [hd, ← hlr, ← v5HopfConv_assoc, hal]
  rw [hlr]
  exact DFunLike.congr_fun hm.symm x

/-- Coaction on a component, transported from the regular identity-component action. -/
def v5ComponentRegularCoaction (P I : Ideal H)
    (E : (H ⧸ P) ≃ₐ[k] (H ⧸ I))
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I)) :
    H ⧸ P →ₐ[k] (H ⧸ P) ⊗[k] (H ⧸ I) :=
  (Algebra.TensorProduct.map E.symm.toAlgHom (AlgHom.id k (H ⧸ I))).comp
    (ΔI.comp E.toAlgHom)

theorem v5ComponentRegularCoaction_intertwines (P I : Ideal H)
    (E : (H ⧸ P) ≃ₐ[k] (H ⧸ I))
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I)) (x : H ⧸ P) :
    Algebra.TensorProduct.map E.toAlgHom (AlgHom.id k (H ⧸ I))
      (v5ComponentRegularCoaction P I E ΔI x) = ΔI (E x) := by
  have h : (Algebra.TensorProduct.map E.toAlgHom (AlgHom.id k (H ⧸ I))).comp
      (Algebra.TensorProduct.map E.symm.toAlgHom (AlgHom.id k (H ⧸ I))) =
      AlgHom.id k ((H ⧸ I) ⊗[k] (H ⧸ I)) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro a b
    simp
  exact DFunLike.congr_fun h (ΔI (E x))

theorem v5ComponentRegularCoaction_mk (P I : Ideal H)
    (p : H →ₐ[k] k) (E : (H ⧸ P) ≃ₐ[k] (H ⧸ I))
    (hE : ∀ x, E (Ideal.Quotient.mk P x) = Ideal.Quotient.mk I (v5HopfTranslate p x))
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I))
    (hΔ : ∀ x, ΔI (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
        (Bialgebra.comulAlgHom k H x)) (x : H) :
    v5ComponentRegularCoaction P I E ΔI (Ideal.Quotient.mk P x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k P) (Ideal.Quotient.mkₐ k I)
        (Bialgebra.comulAlgHom k H x) := by
  have hcomp : (Algebra.TensorProduct.map E.symm.toAlgHom (AlgHom.id k (H ⧸ I))).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).comp
        (Algebra.TensorProduct.map (v5HopfTranslate p) (AlgHom.id k H))) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k P) (Ideal.Quotient.mkₐ k I) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro a b
    simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_algHom, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [← hE, E.symm_apply_apply]
  change (Algebra.TensorProduct.map E.symm.toAlgHom (AlgHom.id k (H ⧸ I)))
    (ΔI (E (Ideal.Quotient.mk P x))) = _
  rw [hE, hΔ, v5HopfTranslate_comul]
  exact DFunLike.congr_fun hcomp (Bialgebra.comulAlgHom k H x)

end StrictEUnit
#print axioms StrictEUnit.v5ComponentTranslate_ideal
#print axioms StrictEUnit.v5ComponentTranslateEquiv

#print axioms StrictEUnit.v5HopfTranslate_comul

#print axioms StrictEUnit.v5ComponentRegularCoaction
#print axioms StrictEUnit.v5ComponentRegularCoaction_intertwines
#print axioms StrictEUnit.v5ComponentRegularCoaction_mk

#print axioms StrictEUnit.v5HopfComponentEquiv
#print axioms StrictEUnit.v5HopfComponentEquiv_mk
