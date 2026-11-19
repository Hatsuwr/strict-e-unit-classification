import GlobalClassBaseEquation

noncomputable section
open scoped Classical
open Polynomial
namespace StrictEUnit
variable {K C : Type*} {I : C → Type*} {J : Type*}
  [Field K] [CharZero K] [Fintype C] [DecidableEq C]
  [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] [Fintype J] [DecidableEq J]

def classBlockAlgHom : (∀ c, Matrix (I c) (I c) K) →ₐ[K]
    Matrix (Σ c, I c) (Σ c, I c) K :=
  { Matrix.blockDiagonal'RingHom I K with
    commutes' := by
      intro x
      change Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ : I c => x)) = Matrix.diagonal (fun _ => x)
      apply Matrix.ext
      intro ⟨c,i⟩ ⟨b,j⟩
      by_cases h : c = b
      · subst b
        simp [Matrix.blockDiagonal'_apply_eq, Matrix.diagonal]
      · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h, Matrix.diagonal, h] }

theorem reindexedClassResidue_root
    (xi : C → K) (L : ∀ c, Matrix (I c) (I c) K)
    (hL : ∀ c, IsNilpotent (L c)) (e : (Σ c, I c) ≃ J)
    (a : K) (ha : (minpoly K (reindexedClassResidue xi L e)).IsRoot a) :
    ∃ c, a = xi c := by
  choose n hn using hL
  let f : C → K[X] := fun c => (X - Polynomial.C (xi c)) ^ n c
  let p : K[X] := ∏ c, f c
  have hf : ∀ c, aeval (Matrix.diagonal (fun _ : I c => xi c) + L c) (f c) = 0 := by
    intro c
    simpa [f, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, add_sub_cancel_left] using hn c
  have hp : ∀ c, aeval (Matrix.diagonal (fun _ : I c => xi c) + L c) p = 0 := by
    intro c
    have hd : f c ∣ p := Finset.dvd_prod_of_mem f (Finset.mem_univ c)
    obtain ⟨q,hq⟩ := hd
    rw [hq, map_mul, hf c, zero_mul]
  have hpPi : aeval (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) p = 0 := by
    funext c
    exact (aeval_pi_apply₂ _ _ c).trans (hp c)
  have hpB : aeval (Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c)) p = 0 := by
    rw [show Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) =
      classBlockAlgHom (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) from rfl,
      aeval_algHom_apply, hpPi, map_zero]
  have hpM : aeval (reindexedClassResidue xi L e) p = 0 := by
    rw [reindexedClassResidue, aeval_algHom_apply, hpB, map_zero]
  have hd := minpoly.dvd K (reindexedClassResidue xi L e) hpM
  have hpa : p.IsRoot a := eval_eq_zero_of_dvd_of_eval_eq_zero hd ha
  obtain ⟨c,_,hc⟩ := (isRoot_prod Finset.univ f a).mp hpa
  refine ⟨c, ?_⟩
  have hz : (a - xi c) ^ n c = 0 := by simpa [IsRoot, f] using hc
  exact sub_eq_zero.mp (pow_eq_zero hz)

theorem reindexedClassResidue_rational_spectrum
    (xi : C → K) (hxi : ∀ c, ∃ q : ℚ, (q : K) = xi c)
    (L : ∀ c, Matrix (I c) (I c) K) (hL : ∀ c, IsNilpotent (L c))
    (e : (Σ c, I c) ≃ J) (a : K)
    (ha : (minpoly K (reindexedClassResidue xi L e)).IsRoot a) :
    ∃ q : ℚ, (q : K) = a := by
  obtain ⟨c,rfl⟩ := reindexedClassResidue_root xi L hL e a ha
  exact hxi c
end StrictEUnit
end
