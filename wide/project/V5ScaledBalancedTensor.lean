import V5BalancedEulerDerivation128

noncomputable section
open scoped TensorProduct
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

/-- Exact balance follows from ordinary source compatibility and q-scaled
compatibility on the ramified target. -/
theorem v5_scaled_tensor_balance129
    {k B S D : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing D]
    [Algebra k B] [Algebra k S] [Algebra k D] [Algebra B S] [Algebra B D]
    (δ : Derivation k B B) (dS : Derivation k S S) (dD : Derivation k D D) (q : ℕ)
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (δ b))
    (hD : ∀ b, dD (algebraMap B D b) = q • algebraMap B D (δ b)) :
    ∀ b : B, ((q • dS) (algebraMap B S b)) ⊗ₜ[B] (1 : D) =
      (1 : S) ⊗ₜ[B] dD (algebraMap B D b) := by
  intro b
  change (q • dS (algebraMap B S b)) ⊗ₜ[B] (1 : D) = _
  rw [hS, hD]
  have hb : algebraMap B S (δ b) ⊗ₜ[B] (1 : D) = (1 : S) ⊗ₜ[B] algebraMap B D (δ b) := by
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  clear hD
  induction q with
  | zero => simp
  | succ n hn => simpa only [succ_nsmul, TensorProduct.add_tmul, TensorProduct.tmul_add, hb] using congrArg (fun x => x + ((1 : S) ⊗ₜ[B] algebraMap B D (δ b))) hn

/-- The balanced Kummer tensor operator is constructed, not supplied as an
extra linear-map witness. -/
def v5ScaledBalancedTensorDerivation129
    {k B S D : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing D]
    [Algebra k B] [Algebra k S] [Algebra k D] [Algebra B S] [Algebra B D]
    [Algebra k (S ⊗[B] D)]
    (δ : Derivation k B B) (dS : Derivation k S S) (dD : Derivation k D D) (q : ℕ)
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (δ b))
    (hD : ∀ b, dD (algebraMap B D b) = q • algebraMap B D (δ b))
    (hscalar : ∀ a : k, algebraMap k (S ⊗[B] D) a =
      (algebraMap k S a) ⊗ₜ[B] (1 : D)) :
    Derivation k (S ⊗[B] D) (S ⊗[B] D) :=
  v5BalancedTensorDerivation128 (q • dS) dD
    (v5_scaled_tensor_balance129 δ dS dD q hS hD) hscalar

theorem v5ScaledBalancedTensorDerivation129_tmul
    {k B S D : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing D]
    [Algebra k B] [Algebra k S] [Algebra k D] [Algebra B S] [Algebra B D]
    [Algebra k (S ⊗[B] D)]
    (δ : Derivation k B B) (dS : Derivation k S S) (dD : Derivation k D D) (q : ℕ)
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (δ b))
    (hD : ∀ b, dD (algebraMap B D b) = q • algebraMap B D (δ b))
    (hscalar : ∀ a : k, algebraMap k (S ⊗[B] D) a =
      (algebraMap k S a) ⊗ₜ[B] (1 : D)) (s : S) (d : D) :
    v5ScaledBalancedTensorDerivation129 δ dS dD q hS hD hscalar (s ⊗ₜ[B] d) =
      (q • dS s) ⊗ₜ[B] d + s ⊗ₜ[B] dD d :=
  v5BalancedTensorDerivation128_tmul _ _ _ _ s d

end StrictEUnit
#print axioms StrictEUnit.v5_scaled_tensor_balance129
#print axioms StrictEUnit.v5ScaledBalancedTensorDerivation129
#print axioms StrictEUnit.v5ScaledBalancedTensorDerivation129_tmul
