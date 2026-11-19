import V5BalancedEulerFull

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B S D : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing D]
  [Algebra B S] [Algebra B D] [Algebra k S] [Algebra k D]
  [Algebra k (S ⊗[B] D)]
  (dS : Derivation k S S) (dD : Derivation k D D)
  (hbase : ∀ b : B,
    dS (algebraMap B S b) ⊗ₜ[B] (1 : D) =
      (1 : S) ⊗ₜ[B] dD (algebraMap B D b))
  (hscalar : ∀ a : k, algebraMap k (S ⊗[B] D) a =
    (algebraMap k S a) ⊗ₜ[B] (1 : D))

/-- Balanced Euler operator as a genuine k-derivation. The left factor
may already be scaled by any coefficient, including the Kummer index. -/
def v5BalancedTensorDerivation128 : Derivation k (S ⊗[B] D) (S ⊗[B] D) :=
  Derivation.mk'
    { v5BalancedTensorEuler dS dD hbase with
      map_smul' := by
        intro a x
        change v5BalancedTensorEuler dS dD hbase (a • x) =
          a • v5BalancedTensorEuler dS dD hbase x
        have hzero :
            v5BalancedTensorEuler dS dD hbase (algebraMap k (S ⊗[B] D) a) = 0 := by
          rw [hscalar, v5BalancedTensorEuler_tmul, dS.map_algebraMap, dD.map_one_eq_zero]
          simp
        rw [Algebra.smul_def, v5BalancedTensorEuler_leibniz, hzero, mul_zero, add_zero,
          Algebra.smul_def] }
    (fun x y => by
      change v5BalancedTensorEuler dS dD hbase (x * y) = _
      simpa only [smul_eq_mul] using v5BalancedTensorEuler_leibniz dS dD hbase x y)

theorem v5BalancedTensorDerivation128_tmul (s : S) (d : D) :
    v5BalancedTensorDerivation128 dS dD hbase hscalar (s ⊗ₜ[B] d) =
      dS s ⊗ₜ[B] d + s ⊗ₜ[B] dD d :=
  v5BalancedTensorEuler_tmul dS dD hbase s d

end StrictEUnit
#print axioms StrictEUnit.v5BalancedTensorDerivation128
#print axioms StrictEUnit.v5BalancedTensorDerivation128_tmul
