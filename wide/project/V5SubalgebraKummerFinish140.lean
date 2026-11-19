import V5SubalgebraKummerFirstOrder136
noncomputable section
set_option Elab.async false
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 800000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
variable {k B R H W L C : Type*}
  [Field k] [CommRing B] [CommRing R] [CommRing H] [CommRing W]
  [CommRing L] [IsDomain L] [IsPrincipalIdealRing L] [CommRing C]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k H] [Algebra k W] [Algebra B W] [IsScalarTower k B W]
  [Algebra k L] [Algebra k C]

theorem v5SubalgebraKummerFinish140
    (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H)
    (dB0 : Derivation k B B) (dR0 : Derivation k R R)
    (hBR0 : ∀ b, dR0 (algebraMap B R b) = algebraMap B R (dB0 b))
    (hd : ∀ r, tensorDerivation dR0 (ρ r) = ρ (dR0 r))
    (dW0 : Derivation k W W)
    (hBW0 : ∀ b, dW0 (algebraMap B W b) = algebraMap B W (dB0 b))
    (z : B) (q : ℕ) (dL : Derivation k L L)
    (F : B →+* L)
    (α : v5CanonicalComponentCover ρ I →ₐ[k] L)
    (hbase : α.toRingHom.comp (algebraMap B (v5CanonicalComponentCover ρ I)) = F)
    (hEuler : ∀ t, dL (α t) = (q : L) * α (v5CoordinateEuler136 z
      (v5ComponentCoverDerivation126 ρ (Ideal.Quotient.mkₐ k I) dR0 hd) t))
    (eRel : R ⊗[v5CanonicalComponentCover ρ I] R ≃ₐ[R] R ⊗[k] (H ⧸ I))
    (heRel : ∀ a b, eRel (a ⊗ₜ[v5CanonicalComponentCover ρ I] b) =
      a • v5ComponentOwnAction ρ (Ideal.Quotient.mkₐ k I) b)
    (hFF : Module.FaithfullyFlat (v5CanonicalComponentCover ρ I) R)
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t : v5CanonicalComponentCover ρ I, pL (α t) = pR (t : R))
    (pW : W →ₐ[k] C)
    (hRmark : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b))
    (u : (R ⊗[B] W)ˣ) (a c : C)
    (hu0 : mixedRelativeTensorDerivation dB0 dR0 dW0 hBR0 hBW0 (u : R ⊗[B] W) = 0)
    {Q : C → C → Prop}
    (finish : ∀ [Algebra B L] [IsScalarTower k B L],
      (∀ b, algebraMap B L b = F b) →
      ∀ hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b),
      ∀ D : L ⊗[B] W →+ L ⊗[B] W,
      (∀ l w, D (l ⊗ₜ[B] w) = dL l ⊗ₜ[B] w +
        l ⊗ₜ[B] (algebraMap B W ((q : B) * z) * dW0 w)) →
      (∃ b : (L ⊗[B] W)ˣ,
        v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
        v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
        ∃ ell : L, D (b : L ⊗[B] W) =
          (ell ⊗ₜ[B] (1 : W)) * (b : L ⊗[B] W)) → Q a c) :
  let T := v5CanonicalComponentCover ρ I
  let τ := v5CoverRestrictedCoaction135 ρ I
  letI : Module.FaithfullyFlat T R := hFF
  letI : IsScalarTower k T R :=
    IsScalarTower.of_algebraMap_eq (fun x => ((T.val.restrictScalars k).commutes x).symm)
  letI : Algebra T L := α.toAlgebra
  letI : IsScalarTower k T L :=
    IsScalarTower.of_algebraMap_eq (fun x => (α.commutes x).symm)
  letI : Algebra B L := (α.toRingHom.comp (algebraMap B T)).toAlgebra
  letI : IsScalarTower B T L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k L x = α (algebraMap B T (algebraMap k B x))
    rw [← IsScalarTower.algebraMap_apply k B T, α.commutes])
  (∃ χ : (H ⧸ I)ˣ, V5KummerLiftResult136 τ pL pR pW hm hRmark u a c χ) → Q a c := by
  let T := v5CanonicalComponentCover ρ I
  let dT0 : Derivation k T T := v5ComponentCoverDerivation126 ρ (Ideal.Quotient.mkₐ k I) dR0 hd
  let τ := v5CoverRestrictedCoaction135 ρ I
  letI : Module.FaithfullyFlat T R := hFF
  letI : IsScalarTower k T R :=
    IsScalarTower.of_algebraMap_eq (fun x => ((T.val.restrictScalars k).commutes x).symm)
  letI : Algebra T L := α.toAlgebra
  letI : IsScalarTower k T L :=
    IsScalarTower.of_algebraMap_eq (fun x => (α.commutes x).symm)
  letI : Algebra B L := (α.toRingHom.comp (algebraMap B T)).toAlgebra
  letI : IsScalarTower B T L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k L x = α (algebraMap B T (algebraMap k B x))
    rw [← IsScalarTower.algebraMap_apply k B T, α.commutes])
  let hα := v5CoordinateEuler_scaled_map136 (k := k) (B := B)
    (U := T) (L := L) z dT0 q dL α hEuler
  let coeff := (q : B) * z
  let data := v5SubalgebraScaledKummerData136 ρ I dB0 dR0 hBR0 hd dW0 hBW0 coeff dL α hα
    (u : R ⊗[B] W) hu0
  let D := v5ScaledKummerCoeffDerivation136 dB0 dT0 dR0 dW0 dL coeff τ (u : R ⊗[B] W) data
  let hB := v5KummerBaseMarks136 pL pR pW hm hRmark
  change (∃ χ : (H ⧸ I)ˣ, V5KummerLiftResult136 τ pL pR pW hm hRmark u a c χ) → Q a c
  intro hlift
  obtain ⟨χ, hχ⟩ := hlift
  apply @finish (inferInstance : Algebra B L) (inferInstance : IsScalarTower k B L)
    (fun b => RingHom.congr_fun hbase b) hB D.toAddMonoidHom
  · intro l w
    exact v5ScaledKummerCoeffDerivation136_tmul dB0 dT0 dR0 dW0 dL coeff τ (u : R ⊗[B] W) data l w
  · exact v5KummerLiftFirstOrderOfData136 τ eRel heRel pL pR pW hm hRmark u a c χ hχ
      dB0 dT0 dL dR0 dW0 coeff data
end StrictEUnit
#print axioms StrictEUnit.v5SubalgebraKummerFinish140
