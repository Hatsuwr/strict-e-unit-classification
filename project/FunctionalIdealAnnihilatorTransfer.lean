import MatrixPolynomialDifferentialGauge

/-! Transfer the exact annihilator encoded in the whole functional relation
ideal. This uses neither a tensor-product annihilator nor minimality. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
section Evaluation
variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]

theorem mvSystemD_eval₂_iterate
    (d : R →+ R) (e : S →+ S) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (f : R →+* S) (hf : ∀ a, e (f a) = f (d a))
    (A : Matrix ι ι R) (y : ι → S)
    (hy : ∀ i, e (y i) = ∑ j, f (A i j) * y j)
    (n : ℕ) (P : MvPolynomial ι R) :
    MvPolynomial.eval₂Hom f y ((mvSystemD d A : MvPolynomial ι R → MvPolynomial ι R)^[n] P) =
      (e : S → S)^[n] (MvPolynomial.eval₂Hom f y P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [← mvSystemD_eval₂ d e h1 hd he f hf A y hy, ih]

def mvSystemAnnihilator
    (d : R →+ R) (A : Matrix ι ι R)
    (m : ℕ) (c : Fin (m+1) → R) (P : MvPolynomial ι R) : MvPolynomial ι R :=
  ∑ i, MvPolynomial.C (c i) *
    (mvSystemD d A : MvPolynomial ι R → MvPolynomial ι R)^[i.val] P

theorem mvSystemAnnihilator_eval₂
    (d : R →+ R) (e : S →+ S) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (f : R →+* S) (hf : ∀ a, e (f a) = f (d a))
    (A : Matrix ι ι R) (y : ι → S)
    (hy : ∀ i, e (y i) = ∑ j, f (A i j) * y j)
    (m : ℕ) (c : Fin (m+1) → R) (P : MvPolynomial ι R) :
    MvPolynomial.eval₂Hom f y (mvSystemAnnihilator d A m c P) =
      ∑ i, f (c i) * (e : S → S)^[i.val] (MvPolynomial.eval₂Hom f y P) := by
  simp only [mvSystemAnnihilator, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    mvSystemD_eval₂_iterate d e h1 hd he f hf A y hy]

end Evaluation

/-- Every exact scalar annihilator expressed in the actual functional kernel
transfers to a target solution annihilating that kernel. No minimality is needed. -/
theorem functionalIdeal_scaled_annihilator_transfer
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T] [Fintype ι]
    (d : R →+ R) (e : S →+ S) (e' : T →+ T) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (he' : ∀ a b, e' (a * b) = a * e' b + b * e' a)
    (f : R →+* S) (g : R →+* T)
    (hf : ∀ a, e (f a) = f (d a)) (hg : ∀ a, e' (g a) = g (d a))
    (A : Matrix ι ι R) (y : ι → S) (v : ι → T)
    (hy : ∀ i, e (y i) = ∑ j, f (A i j) * y j)
    (hv : ∀ i, e' (v i) = ∑ j, g (A i j) * v j)
    (hkernel : mvFunctionalIdeal f y ≤ mvFunctionalIdeal g v)
    (a : R) (P : MvPolynomial ι R) (m : ℕ) (c : Fin (m+1) → R)
    (hsource : (∑ i, f (c i) * (e : S → S)^[i.val]
      (f a * MvPolynomial.eval₂Hom f y P)) = 0) :
    (∑ i, g (c i) * (e' : T → T)^[i.val]
      (g a * MvPolynomial.eval₂Hom g v P)) = 0 := by
  let Q := mvSystemAnnihilator d A m c (MvPolynomial.C a * P)
  have hQ : Q ∈ mvFunctionalIdeal f y := by
    change MvPolynomial.eval₂Hom f y Q = 0
    rw [mvSystemAnnihilator_eval₂ d e h1 hd he f hf A y hy]
    simpa only [map_mul, MvPolynomial.eval₂Hom_C] using hsource
  have hQ' := hkernel hQ
  change MvPolynomial.eval₂Hom g v Q = 0 at hQ'
  rw [mvSystemAnnihilator_eval₂ d e' h1 hd he' g hg A v hv] at hQ'
  simpa only [map_mul, MvPolynomial.eval₂Hom_C] using hQ'

end StrictEUnit
