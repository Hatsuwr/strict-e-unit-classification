import MonomialEulerPresentation

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The literal gauged matrix acts on the literal weighted vector by the
Leibniz formula. This is an identity for EVERY vector, not just solutions. -/
theorem monomialEulerConnection_weighted_action {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (v : Fin r → LaurentSeries K) (i : Fin r) :
    (∑ j,monomialEulerConnection A w i j*(laurentIntegerMonomial (w j : ℤ)*v j))=
      (w i : LaurentSeries K)*(laurentIntegerMonomial (w i : ℤ)*v i)+
      laurentIntegerMonomial ((w i+1 : ℕ) : ℤ)*(∑ j,A i j*v j) := by
  have ht (j : Fin r) : monomialEulerConnection A w i j*(laurentIntegerMonomial (w j : ℤ)*v j)=
      (if i=j then (w i : LaurentSeries K)*(laurentIntegerMonomial (w i : ℤ)*v i) else 0)+
      laurentIntegerMonomial ((w i+1 : ℕ) : ℤ)*(A i j*v j) := by
    simp only [monomialEulerConnection,add_mul,Matrix.one_apply]
    have hm : laurentIntegerMonomial (K:=K) ((w i : ℤ)+1-(w j : ℤ))*laurentIntegerMonomial (w j : ℤ)=
        laurentIntegerMonomial ((w i+1 : ℕ) : ℤ) := by
      rw [laurentIntegerMonomial_mul];congr 1;push_cast;omega
    by_cases hij : i=j
    · subst j
      simp only [ite_true,mul_one]
      rw [show laurentIntegerMonomial (K:=K) ((w i : ℤ)+1-(w i : ℤ))*A i i*
          (laurentIntegerMonomial (w i : ℤ)*v i)=
          (laurentIntegerMonomial ((w i : ℤ)+1-(w i : ℤ))*laurentIntegerMonomial (w i : ℤ))*(A i i*v i) by ring,hm]
    · simp only [hij,ite_false,mul_zero,zero_mul,zero_add]
      calc
        _=(laurentIntegerMonomial (K:=K) ((w i : ℤ)+1-(w j : ℤ))*laurentIntegerMonomial (w j : ℤ))*(A i j*v j) := by ring
        _=_ := by rw [hm]
  simp_rw [ht]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.mul_sum]

/-- Complete solution equivalence under an exactly identified regular Euler
presentation. Weighting by nonzero monomials is reversible even with poles. -/
theorem monomialEulerPresentation_solution_iff {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hreal : monomialEulerConnection A w=C.map (HahnSeries.ofPowerSeries ℤ K))
    (v : Fin r → LaurentSeries K) :
    (∀ i,stage14_laurentAlgebraDerivation (v i)=∑ j,A i j*v j) ↔
      ∀ i,laurentEuler (laurentIntegerMonomial (w i : ℤ)*v i)=
        ∑ j,HahnSeries.ofPowerSeries ℤ K (C i j)*(laurentIntegerMonomial (w j : ℤ)*v j) := by
  have hsum (i : Fin r) := monomialEulerConnection_weighted_action A w v i
  rw [hreal] at hsum
  simp only [Matrix.map_apply] at hsum
  constructor
  · intro h i
    rw [laurentEuler_integer_shear_step,← stage14_laurentAlgebraDerivation_apply,h i]
    exact (hsum i).symm
  · intro h i
    have hi := h i
    rw [laurentEuler_integer_shear_step,← stage14_laurentAlgebraDerivation_apply,hsum i] at hi
    exact mul_left_cancel₀ (laurentIntegerMonomial_ne_zero _) (add_left_cancel hi)

end StrictEUnit
end
