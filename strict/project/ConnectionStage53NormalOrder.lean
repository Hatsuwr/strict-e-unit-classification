import ConnectionMixedLeibniz
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
theorem connection_mixed_leibniz (d : Derivation K A A)
    (D : A →ₗ[K] A) (hd : ∀ x y,D (x*y)=d x*y+x*D y) (z : A)
    (hz : d z = 1) (P : Polynomial K) (y : A) (ν j : ℕ) (hj : j ≤ ν) :
    (D : A → A)^[j] (Polynomial.aeval z P * y) =
      ∑ l : Fin (ν+1), (j.choose l.val) •
        (Polynomial.aeval z
          ((Polynomial.derivative : Polynomial K → Polynomial K)^[j-l.val] P) *
            (D : A → A)^[l.val] y) := by
  rw [connection_iterate_leibniz d D hd,
    Fin.sum_univ_eq_sum_range (fun l : ℕ => (j.choose l) •
      (Polynomial.aeval z
        ((Polynomial.derivative : Polynomial K → Polynomial K)^[j-l] P) *
          (D : A → A)^[l] y))]
  simp_rw [logFourier_iterate_aeval d z hz]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hj))
  intro l _ hnot
  have hlt : j < l := by simp only [Finset.mem_range] at hnot; omega
  simp [Nat.choose_eq_zero_of_lt hlt]

variable [CharZero K]
theorem connection_stage53_normal_ordering {mu nu : ℕ}
    (d : Derivation K A A) (D : A →ₗ[K] A)
    (hd : ∀ x y,D (x*y)=d x*y+x*D y) (z : A) (hz : d z=1)
    (a : Fin (mu+1) →Fin (nu+1) →K) (y : A) :
    (∑ i,∑ j,algebraMap K A ((-1 : K)^j.val*a i j)*
      (D : A →A)^[j.val] (z^i.val*y)) =
      ∑ l,Polynomial.aeval z (stage53_fourierCoeff a l)*(D : A →A)^[l.val] y := by
  classical
  have h (i : Fin (mu+1)) (j : Fin (nu+1)) :=
    connection_mixed_leibniz d D hd z hz (Polynomial.X^i.val : Polynomial K) y nu j.val (by omega)
  simp only [map_pow,Polynomial.aeval_X] at h
  simp_rw [stage53_fourierCoeff_eq_unfiltered,map_sum,Finset.sum_mul,
    map_mul,Polynomial.aeval_C,h,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (mu+1))))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [nsmul_eq_mul,map_mul,map_natCast]
  ring
end StrictEUnit
end
