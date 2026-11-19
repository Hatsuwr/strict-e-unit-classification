import LaurentPolynomialIdealDescent
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Data.Matrix.Basic

/-!
Finite-variable polynomial gauge straightening for differential ideals.

The substitution is P(Y) -> P(W X), with the actual matrix equation W' = A W.
The coefficient derivative, system derivative, evaluation chain rule, coefficient
extension, and ideal-map stability are proved separately. Invertibility of W is
used only to construct a substitution equivalence, not for differential stability.

No absolute primality, numerical-specialization injectivity, equality with a
numerical relation ideal, or Picard--Vessiot torsor premise is asserted here.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix

namespace StrictEUnit

section CoefficientDerivative

variable {R σ : Type*} [CommRing R]

def mvCoeffD (d : R →+ R) :
    MvPolynomial σ R →+ MvPolynomial σ R :=
  Finsupp.mapRange.addMonoidHom d

@[simp] theorem mvCoeffD_coeff
    (d : R →+ R) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (mvCoeffD d P) =
      d (MvPolynomial.coeff m P) := rfl

@[simp] theorem mvCoeffD_monomial
    (d : R →+ R) (m : σ →₀ ℕ) (a : R) :
    mvCoeffD d (MvPolynomial.monomial m a) =
      MvPolynomial.monomial m (d a) := by
  change Finsupp.mapRange d d.map_zero (Finsupp.single m a) =
    Finsupp.single m (d a)
  exact Finsupp.mapRange_single

@[simp] theorem mvCoeffD_C (d : R →+ R) (a : R) :
    mvCoeffD (σ := σ) d (MvPolynomial.C a) =
      MvPolynomial.C (d a) :=
  mvCoeffD_monomial d 0 a

theorem mvCoeffD_X (d : R →+ R) (h1 : d 1 = 0) (i : σ) :
    mvCoeffD d (MvPolynomial.X i) = 0 := by
  rw [MvPolynomial.X, mvCoeffD_monomial, h1,
    MvPolynomial.monomial_zero]

/-- This identity needs neither a product rule nor d(1)=0. -/
theorem mvCoeffD_C_mul_X (d : R →+ R) (a : R) (i : σ) :
    mvCoeffD d (MvPolynomial.C a * MvPolynomial.X i) =
      MvPolynomial.C (d a) * MvPolynomial.X i := by
  rw [MvPolynomial.C_mul_X_eq_monomial, mvCoeffD_monomial,
    MvPolynomial.C_mul_X_eq_monomial]

theorem mvCoeffD_mul
    (d : R →+ R)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (P Q : MvPolynomial σ R) :
    mvCoeffD d (P * Q) =
      P * mvCoeffD d Q + Q * mvCoeffD d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m a =>
      induction Q using MvPolynomial.induction_on' with
      | monomial n b =>
          simp only [MvPolynomial.monomial_mul, mvCoeffD_monomial,
            hd, map_add, add_comm n m]
      | add Q T hQ hT =>
          simp only [mul_add, map_add, hQ, hT, add_mul]
          ring
  | add P T hP hT =>
      simp only [add_mul, map_add, hP, hT, mul_add]
      ring

end CoefficientDerivative

/-- A ring hom intertwines additive derivations once this is checked on
coefficient constants and polynomial variables. -/
theorem mvPolynomial_differential_hom
    {R S σ : Type*} [CommRing R] [CommRing S]
    (D : MvPolynomial σ R →+ MvPolynomial σ R)
    (e : S →+ S)
    (hD : ∀ P Q, D (P * Q) = P * D Q + Q * D P)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (φ : MvPolynomial σ R →+* S)
    (hC : ∀ a, e (φ (MvPolynomial.C a)) =
      φ (D (MvPolynomial.C a)))
    (hX : ∀ i, e (φ (MvPolynomial.X i)) =
      φ (D (MvPolynomial.X i)))
    (P : MvPolynomial σ R) :
    e (φ P) = φ (D P) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact hC a
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, he, hP, hX, hD, map_add, map_mul, map_mul]

section MatrixPolynomial

variable {R ι : Type*} [CommRing R] [Fintype ι]

def matrixLinearForm (A : Matrix ι ι R) (i : ι) :
    MvPolynomial ι R :=
  ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

def matrixPolynomialSubst (W : Matrix ι ι R) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval (matrixLinearForm W)

@[simp] theorem matrixPolynomialSubst_C
    (W : Matrix ι ι R) (a : R) :
    matrixPolynomialSubst W (MvPolynomial.C a) =
      MvPolynomial.C a := by
  simp only [matrixPolynomialSubst, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq]

@[simp] theorem matrixPolynomialSubst_X
    (W : Matrix ι ι R) (i : ι) :
    matrixPolynomialSubst W (MvPolynomial.X i) =
      matrixLinearForm W i :=
  MvPolynomial.aeval_X _ _

theorem mvCoeffD_matrixLinearForm
    (d : R →+ R) (W : Matrix ι ι R) (i : ι) :
    mvCoeffD d (matrixLinearForm W i) =
      matrixLinearForm (W.map d) i := by
  simp only [matrixLinearForm, map_sum, mvCoeffD_C_mul_X,
    Matrix.map_apply]

theorem matrixPolynomialSubst_linearForm
    (U W : Matrix ι ι R) (i : ι) :
    matrixPolynomialSubst W (matrixLinearForm U i) =
      matrixLinearForm (U * W) i := by
  classical
  calc
    matrixPolynomialSubst W (matrixLinearForm U i)
        = ∑ j, ∑ k,
            MvPolynomial.C (U i j) *
              (MvPolynomial.C (W j k) * MvPolynomial.X k) := by
          simp only [matrixLinearForm, map_sum, map_mul,
            matrixPolynomialSubst_C, matrixPolynomialSubst_X,
            Finset.mul_sum]
    _ = ∑ k, ∑ j,
          MvPolynomial.C (U i j * W j k) * MvPolynomial.X k := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro j _
          rw [map_mul, mul_assoc]
    _ = matrixLinearForm (U * W) i := by
          simp only [matrixLinearForm, Matrix.mul_apply,
            map_sum, Finset.sum_mul]

/-- Composition reverses the order of the matrices. -/
theorem matrixPolynomialSubst_comp
    (U W : Matrix ι ι R) :
    (matrixPolynomialSubst W).comp (matrixPolynomialSubst U) =
      matrixPolynomialSubst (U * W) := by
  apply MvPolynomial.algHom_ext
  intro i
  change matrixPolynomialSubst W
      (matrixPolynomialSubst U (MvPolynomial.X i)) =
    matrixPolynomialSubst (U * W) (MvPolynomial.X i)
  rw [matrixPolynomialSubst_X, matrixPolynomialSubst_linearForm,
    matrixPolynomialSubst_X]

variable [DecidableEq ι]

@[simp] theorem matrixLinearForm_one (i : ι) :
    matrixLinearForm (1 : Matrix ι ι R) i = MvPolynomial.X i := by
  simp [matrixLinearForm, Matrix.one_apply]

@[simp] theorem matrixPolynomialSubst_one :
    matrixPolynomialSubst (1 : Matrix ι ι R) =
      AlgHom.id R (MvPolynomial ι R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

def matrixPolynomialGaugeEquiv (u : (Matrix ι ι R)ˣ) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R :=
  AlgEquiv.ofAlgHom
    (matrixPolynomialSubst (u : Matrix ι ι R))
    (matrixPolynomialSubst ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R))
    (by rw [matrixPolynomialSubst_comp]; simp)
    (by rw [matrixPolynomialSubst_comp]; simp)

theorem matrixPolynomialSubst_bijective
    (W : Matrix ι ι R) (hW : IsUnit W) :
    Function.Bijective (matrixPolynomialSubst W) := by
  rcases hW with ⟨u, rfl⟩
  exact (matrixPolynomialGaugeEquiv u).bijective

end MatrixPolynomial

section MatrixSystemDerivative

variable {R ι : Type*} [CommRing R] [Fintype ι]

def mvSystemD (d : R →+ R) (A : Matrix ι ι R) :
    MvPolynomial ι R →+ MvPolynomial ι R :=
  mvCoeffD d +
    (MvPolynomial.mkDerivation R
      (matrixLinearForm A)).toLinearMap.toAddMonoidHom

theorem mvSystemD_C
    (d : R →+ R) (A : Matrix ι ι R) (a : R) :
    mvSystemD d A (MvPolynomial.C a) =
      MvPolynomial.C (d a) := by
  change mvCoeffD d (MvPolynomial.C a) +
    MvPolynomial.mkDerivation R (matrixLinearForm A)
      (MvPolynomial.C a) = _
  rw [mvCoeffD_C, MvPolynomial.derivation_C, add_zero]

theorem mvSystemD_X
    (d : R →+ R) (h1 : d 1 = 0)
    (A : Matrix ι ι R) (i : ι) :
    mvSystemD d A (MvPolynomial.X i) =
      matrixLinearForm A i := by
  change mvCoeffD d (MvPolynomial.X i) +
    MvPolynomial.mkDerivation R (matrixLinearForm A)
      (MvPolynomial.X i) = _
  rw [mvCoeffD_X d h1, MvPolynomial.mkDerivation_X, zero_add]

theorem mvSystemD_mul
    (d : R →+ R)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (A : Matrix ι ι R) (P Q : MvPolynomial ι R) :
    mvSystemD d A (P * Q) =
      P * mvSystemD d A Q + Q * mvSystemD d A P := by
  let V := MvPolynomial.mkDerivation R (matrixLinearForm A)
  change mvCoeffD d (P * Q) + V (P * Q) =
    P * (mvCoeffD d Q + V Q) + Q * (mvCoeffD d P + V P)
  rw [mvCoeffD_mul d hd, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem matrixPolynomialSubst_differential
    (d : R →+ R) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (A W : Matrix ι ι R) (hW : W.map d = A * W)
    (P : MvPolynomial ι R) :
    mvCoeffD d (matrixPolynomialSubst W P) =
      matrixPolynomialSubst W (mvSystemD d A P) := by
  apply mvPolynomial_differential_hom
    (mvSystemD d A) (mvCoeffD d)
    (mvSystemD_mul d hd A) (mvCoeffD_mul d hd)
    (matrixPolynomialSubst W).toRingHom
  · intro a
    change mvCoeffD d (matrixPolynomialSubst W (MvPolynomial.C a)) =
      matrixPolynomialSubst W (mvSystemD d A (MvPolynomial.C a))
    rw [matrixPolynomialSubst_C, mvCoeffD_C,
      mvSystemD_C, matrixPolynomialSubst_C]
  · intro i
    change mvCoeffD d (matrixPolynomialSubst W (MvPolynomial.X i)) =
      matrixPolynomialSubst W (mvSystemD d A (MvPolynomial.X i))
    rw [matrixPolynomialSubst_X, mvCoeffD_matrixLinearForm,
      mvSystemD_X d h1, matrixPolynomialSubst_linearForm, hW]

end MatrixSystemDerivative

/-- Extension of an invariant ideal along a differential ring hom is invariant.
Neither injectivity nor surjectivity of the ring hom is needed. -/
theorem additive_differential_ideal_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : R →+ R) (e : S →+ S)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (hf : ∀ x, e (f x) = f (d x))
    (I : Ideal R)
    (hI : ∀ x, x ∈ I → d x ∈ I) :
    ∀ y, y ∈ I.map f → e y ∈ I.map f := by
  let J : Ideal S := I.map f
  let J' : Ideal S :=
    { carrier := {y | y ∈ J ∧ e y ∈ J}
      zero_mem' := ⟨J.zero_mem, by
        rw [map_zero]
        exact J.zero_mem⟩
      add_mem' := by
        intro a b ha hb
        refine ⟨J.add_mem ha.1 hb.1, ?_⟩
        rw [map_add]
        exact J.add_mem ha.2 hb.2
      smul_mem' := by
        intro a b hb
        change a * b ∈ J ∧ e (a * b) ∈ J
        refine ⟨J.mul_mem_left a hb.1, ?_⟩
        rw [he]
        exact J.add_mem
          (J.mul_mem_left a hb.2)
          (J.mul_mem_right (e a) hb.1) }
  have hle : J ≤ J' := by
    change I.map f ≤ J'
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change f x ∈ J ∧ e (f x) ∈ J
    refine ⟨Ideal.mem_map_of_mem f hx, ?_⟩
    rw [hf]
    exact Ideal.mem_map_of_mem f (hI x hx)
  intro y hy
  exact (hle hy).2

theorem matrixPolynomialSubst_ideal_stable
    {R ι : Type*} [CommRing R] [Fintype ι]
    (d : R →+ R) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (A W : Matrix ι ι R) (hW : W.map d = A * W)
    (I : Ideal (MvPolynomial ι R))
    (hI : ∀ P, P ∈ I → mvSystemD d A P ∈ I) :
    ∀ P, P ∈ I.map (matrixPolynomialSubst W).toRingHom →
      mvCoeffD d P ∈ I.map (matrixPolynomialSubst W).toRingHom :=
  additive_differential_ideal_map
    (matrixPolynomialSubst W).toRingHom
    (mvSystemD d A) (mvCoeffD d)
    (mvCoeffD_mul d hd)
    (matrixPolynomialSubst_differential d h1 hd A W hW)
    I hI

section FunctionalEvaluation

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]

/-- The relation ideal is the kernel of evaluation in an actual function or
fraction-field algebra. It is not evaluation at a numerical point. -/
def mvFunctionalIdeal (f : R →+* S) (y : ι → S) :
    Ideal (MvPolynomial ι R) :=
  RingHom.ker (MvPolynomial.eval₂Hom f y)

theorem mvSystemD_eval₂
    (d : R →+ R) (e : S →+ S)
    (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (f : R →+* S) (hf : ∀ a, e (f a) = f (d a))
    (A : Matrix ι ι R) (y : ι → S)
    (hy : ∀ i, e (y i) = ∑ j, f (A i j) * y j)
    (P : MvPolynomial ι R) :
    e (MvPolynomial.eval₂Hom f y P) =
      MvPolynomial.eval₂Hom f y (mvSystemD d A P) := by
  apply mvPolynomial_differential_hom
    (mvSystemD d A) e (mvSystemD_mul d hd A) he
    (MvPolynomial.eval₂Hom f y)
  · intro a
    rw [MvPolynomial.eval₂Hom_C, mvSystemD_C,
      MvPolynomial.eval₂Hom_C, hf]
  · intro i
    rw [MvPolynomial.eval₂Hom_X', mvSystemD_X d h1, hy]
    simp only [matrixLinearForm, map_sum, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

theorem mvFunctionalIdeal_stable
    (d : R →+ R) (e : S →+ S)
    (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (f : R →+* S) (hf : ∀ a, e (f a) = f (d a))
    (A : Matrix ι ι R) (y : ι → S)
    (hy : ∀ i, e (y i) = ∑ j, f (A i j) * y j) :
    ∀ P, P ∈ mvFunctionalIdeal f y →
      mvSystemD d A P ∈ mvFunctionalIdeal f y := by
  intro P hP
  change MvPolynomial.eval₂Hom f y P = 0 at hP
  change MvPolynomial.eval₂Hom f y (mvSystemD d A P) = 0
  rw [← mvSystemD_eval₂ d e h1 hd he f hf A y hy P, hP, map_zero]

end FunctionalEvaluation

section CoefficientExtension

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]

theorem matrixLinearForm_map
    (f : R →+* S) (A : Matrix ι ι R) (i : ι) :
    MvPolynomial.map f (matrixLinearForm A i) =
      matrixLinearForm (A.map f) i := by
  simp only [matrixLinearForm, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

theorem mvSystemD_map
    (d : R →+ R) (e : S →+ S)
    (hd1 : d 1 = 0) (he1 : e 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (f : R →+* S) (hf : ∀ a, e (f a) = f (d a))
    (A : Matrix ι ι R) (P : MvPolynomial ι R) :
    mvSystemD e (A.map f) (MvPolynomial.map f P) =
      MvPolynomial.map f (mvSystemD d A P) := by
  apply mvPolynomial_differential_hom
    (mvSystemD d A) (mvSystemD e (A.map f))
    (mvSystemD_mul d hd A) (mvSystemD_mul e he (A.map f))
    (MvPolynomial.map f)
  · intro a
    rw [MvPolynomial.map_C, mvSystemD_C, mvSystemD_C,
      MvPolynomial.map_C, hf]
  · intro i
    rw [MvPolynomial.map_X, mvSystemD_X e he1,
      mvSystemD_X d hd1, matrixLinearForm_map]

theorem mvSystemD_ideal_map_stable
    (d : R →+ R) (e : S →+ S)
    (hd1 : d 1 = 0) (he1 : e 1 = 0)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a)
    (he : ∀ a b, e (a * b) = a * e b + b * e a)
    (f : R →+* S) (hf : ∀ a, e (f a) = f (d a))
    (A : Matrix ι ι R) (I : Ideal (MvPolynomial ι R))
    (hI : ∀ P, P ∈ I → mvSystemD d A P ∈ I) :
    ∀ Q, Q ∈ I.map (MvPolynomial.map f) →
      mvSystemD e (A.map f) Q ∈ I.map (MvPolynomial.map f) :=
  additive_differential_ideal_map
    (MvPolynomial.map f) (mvSystemD d A) (mvSystemD e (A.map f))
    (mvSystemD_mul e he (A.map f))
    (mvSystemD_map d e hd1 he1 hd he f hf A) I hI

end CoefficientExtension

end StrictEUnit
end
