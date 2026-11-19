import MatrixDualBinomial
import DerivationDividedLeibniz

/-! Divided higher-connection covariance for an actual diagonal gauge.
The derivative is linear only over its constant field. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k B : Type*} [Field k] [Field B] [Algebra k B]

def matrixRowConnection (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) : (Fin r → B) →ₗ[k] (Fin r → B) where
  toFun v j := d (v j) + ∑ l, v l*A l j
  map_add' v w := by
    funext j
    simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
    abel
  map_smul' c v := by
    funext j
    change d (c • v j)+(∑ l,(c • v l)*A l j)=c • (d (v j)+∑ l,v l*A l j)
    rw [d.map_smul]
    simp only [Algebra.smul_def,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    ring

theorem matrixRowConnection_mul (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (x : B) (v : Fin r → B) :
    matrixRowConnection d A (fun j => x*v j)=
      (fun j => d x*v j+x*matrixRowConnection d A v j) := by
  funext j
  simp only [matrixRowConnection,LinearMap.coe_mk,AddHom.coe_mk,
    Derivation.leibniz,smul_eq_mul,mul_add,Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

theorem matrixRowConnection_iterate_unit (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (m : ℕ) (i : Fin r) :
    ((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[m])
      (fun j => (1 : Matrix (Fin r) (Fin r) B) i j)=
        fun j => matrixConnectionSequence d A m i j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih]
    rfl

theorem matrixRowConnection_iterate_mul (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (m : ℕ) (x : B) (v : Fin r → B) :
    ((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[m]) (fun j => x*v j)=
      ∑ ab ∈ Finset.antidiagonal m, m.choose ab.1 •
        (fun j => (d^[ab.1]) x*
          (((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[ab.2]) v) j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun a b => fun j => (d^[a]) x*
        (((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[b]) v) j) m]
    rw [Function.iterate_succ_apply',ih]
    simp only [map_sum,map_nsmul,matrixRowConnection_mul]
    have hsplit : ∀ a b : ℕ,
        (fun j => d ((d^[a]) x)*(((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[b]) v) j+
          (d^[a]) x*matrixRowConnection d A
            (((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[b]) v) j)=
        (fun j => (d^[a]) x*
          (((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[b+1]) v) j)+
        (fun j => (d^[a+1]) x*
          (((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[b]) v) j) := by
      intro a b; funext j
      simp only [Pi.add_apply,Function.iterate_succ_apply']
      ring
    simp_rw [hsplit,nsmul_add,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    rintro ⟨a,b⟩ hab
    rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hab).symm]

def diagonalGaugeConnection (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (s : Fin r → B) : Matrix (Fin r) (Fin r) B :=
  fun i j => (d (s i)*(1 : Matrix (Fin r) (Fin r) B) i j+s i*A i j)/s j

theorem matrixRowConnection_diagonal_intertwine (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (s : Fin r → B) (hs : ∀ i,s i≠0)
    (v : Fin r → B) :
    matrixRowConnection d A (fun j => v j*s j)=
      fun j => matrixRowConnection d (diagonalGaugeConnection d A s) v j*s j := by
  classical
  funext j
  change d (v j*s j)+(∑ l,v l*s l*A l j)=
    (d (v j)+∑ l,v l*((d (s l)*(1 : Matrix (Fin r) (Fin r) B) l j+s l*A l j)/s j))*s j
  rw [add_mul,Finset.sum_mul]
  have ht (l : Fin r) : v l*((d (s l)*(1 : Matrix (Fin r) (Fin r) B) l j+s l*A l j)/s j)*s j=
      v l*d (s l)*(1 : Matrix (Fin r) (Fin r) B) l j+v l*s l*A l j := by
    field_simp [hs j]
    ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  have he : (∑ l,v l*d (s l)*(1 : Matrix (Fin r) (Fin r) B) l j)=v j*d (s j) := by
    simp [Matrix.one_apply]
  rw [he,Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem matrixConnectionSequence_diagonal_gauge (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (s : Fin r → B) (hs : ∀ i,s i≠0)
    (m : ℕ) (i j : Fin r) :
    matrixConnectionSequence d (diagonalGaugeConnection d A s) m i j*s j=
      ∑ ab ∈ Finset.antidiagonal m,
        (m.choose ab.1 : B)*(d^[ab.1]) (s i)*matrixConnectionSequence d A ab.2 i j := by
  classical
  have hinter (v : Fin r → B) : ∀ n : ℕ,
      ((matrixRowConnection d A : (Fin r → B) → (Fin r → B))^[n]) (fun j => v j*s j)=
        fun j => (((matrixRowConnection d (diagonalGaugeConnection d A s) :
          (Fin r → B) → (Fin r → B))^[n]) v) j*s j := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih,matrixRowConnection_diagonal_intertwine d A s hs]; simp only [Function.iterate_succ_apply']
  have he : (fun j => (1 : Matrix (Fin r) (Fin r) B) i j*s j)=
      fun j => s i*(1 : Matrix (Fin r) (Fin r) B) i j := by
    funext j; by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> subst j <;> rfl
  have h := hinter (fun j => (1 : Matrix (Fin r) (Fin r) B) i j) m
  rw [he,matrixRowConnection_iterate_mul,matrixRowConnection_iterate_unit] at h
  have hj := congrFun h j
  simpa only [Finset.sum_apply,Pi.smul_apply,nsmul_eq_mul,
    matrixRowConnection_iterate_unit,mul_assoc] using hj.symm

theorem matrixConnectionSequence_divided_diagonal_gauge [CharZero B]
    (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (s : Fin r → B) (hs : ∀ i,s i≠0)
    (m : ℕ) (i j : Fin r) :
    matrixConnectionSequence d (diagonalGaugeConnection d A s) m i j/(m.factorial : B)=
      (∑ ab ∈ Finset.antidiagonal m,
        ((d^[ab.1]) (s i)/(ab.1.factorial : B))*
          (matrixConnectionSequence d A ab.2 i j/(ab.2.factorial : B)))/s j := by
  apply (eq_div_iff (hs j)).2
  have h := congrArg (fun x : B => x/(m.factorial : B))
    (matrixConnectionSequence_diagonal_gauge d A s hs m i j)
  dsimp only at h
  rw [Finset.sum_div] at h
  convert h using 1
  · ring
  · apply Finset.sum_congr rfl
    rintro ⟨a,b⟩ hab
    have hn : a+b=m := Finset.mem_antidiagonal.mp hab
    rw [← hn,Nat.cast_add_choose B]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+b))]
    <;> ring

end StrictEUnit
end
