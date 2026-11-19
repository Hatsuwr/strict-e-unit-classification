import V5MixedComparisonEquiv

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R S E n : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S] [Field E]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [Algebra k E] [Algebra B E] [IsScalarTower k B E]
  [Fintype n] [DecidableEq n]

/-- Both relative tensor factors have the expected single system matrix;
no compatibility of their values or choices of bases is assumed. -/
theorem v5_mixed_system_equations
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ) (v : n → S)
    (hY : matrixDerivative dR (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R))
    (hv : ∀ i, dS (v i) = ((algebraMap B S).mapMatrix A).mulVec v i) :
    let d := mixedRelativeTensorDerivation dB dR dS hR hS
    let C := (algebraMap B (R ⊗[B] S)).mapMatrix A
    let W := (v5MixedLeftMatrix (B := B) (S := S) Y : Matrix n n (R ⊗[B] S))
    (matrixDerivative d W = C * W) ∧
      ∀ i, d ((1 : R) ⊗ₜ[B] v i) = (C.mulVec (fun j => (1 : R) ⊗ₜ[B] v j)) i := by
  let d := mixedRelativeTensorDerivation dB dR dS hR hS
  let l : R →ₐ[B] R ⊗[B] S := Algebra.TensorProduct.includeLeft
  let r : S →ₐ[B] R ⊗[B] S := Algebra.TensorProduct.includeRight
  have hl (x : R) : d (l x) = l (dR x) := by
    simp only [d, l, Algebra.TensorProduct.includeLeft_apply, mixedRelativeTensorDerivation_tmul,
      Derivation.map_one_eq_zero, tmul_zero, add_zero]
  have hr (x : S) : d (r x) = r (dS x) := by
    simp only [d, r, Algebra.TensorProduct.includeRight_apply, mixedRelativeTensorDerivation_tmul,
      Derivation.map_one_eq_zero, zero_tmul, zero_add]
  constructor
  · change matrixDerivative d (l.toRingHom.mapMatrix (Y : Matrix n n R)) =
      (algebraMap B (R ⊗[B] S)).mapMatrix A * l.toRingHom.mapMatrix (Y : Matrix n n R)
    rw [matrixDerivative_map dR d _ hl, hY, map_mul]
    congr 1
  · intro i
    change d (r (v i)) = ∑ j, (algebraMap B (R ⊗[B] S) (A i j)) * r (v j)
    rw [hr, hv i]
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum,
      map_mul, AlgHom.commutes]

/-- Mixed comparison driven directly by a matrix solution on R and a generating
vector solution on S over their shared base. -/
def v5MixedSystemComparisonEquiv [Module.Flat B S]
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (dE : Derivation k E E) (f : R →ₐ[B] E) (hf : Function.Injective f)
    (hfD : ∀ r, dE (f r) = f (dR r))
    (hconstants : ∀ a, dE a = 0 → ∃ c : k, algebraMap k E c = a)
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ) (v : n → S)
    (hY : matrixDerivative dR (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R))
    (hv : ∀ i, dS (v i) = ((algebraMap B S).mapMatrix A).mulVec v i)
    (hgen : Algebra.adjoin B (Set.range v) = ⊤) :
    R ⊗[k] derivationConstants (mixedRelativeTensorDerivation dB dR dS hR hS) ≃ₐ[R]
      R ⊗[B] S :=
  let h := v5_mixed_system_equations dB dR dS hR hS A Y v hY hv
  v5MixedComparisonEquiv dB dR dS hR hS dE f hf hfD hconstants
    ((algebraMap B (R ⊗[B] S)).mapMatrix A) Y v h.1 h.2 hgen

end StrictEUnit
#print axioms StrictEUnit.v5_mixed_system_equations
#print axioms StrictEUnit.v5MixedSystemComparisonEquiv
