import FrobeniusScalarRatioBounds

/-! A concrete coefficient size on a fixed logarithmic degree window.
No normed-space instance or change of scalar action is introduced. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

def polynomialLogSize (d : ℕ) (f : Polynomial ℂ) : ℝ :=
  ∑ j : Fin (d+1),‖f.coeff j‖

theorem polynomialLogSize_nonneg (d : ℕ) (f : Polynomial ℂ) : 0 ≤ polynomialLogSize d f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

@[simp] theorem polynomialLogSize_zero (d : ℕ) : polynomialLogSize d 0 = 0 := by
  simp [polynomialLogSize]

theorem polynomialLogSize_coeff_le (d : ℕ) (f : Polynomial ℂ) (j : ℕ)
    (hf : f.natDegree ≤ d) : ‖f.coeff j‖ ≤ polynomialLogSize d f := by
  by_cases hj : j ≤ d
  · let i : Fin (d+1) := ⟨j,by omega⟩
    have h : ‖f.coeff i‖ ≤ ∑ k : Fin (d+1),‖f.coeff k‖ :=
      Finset.single_le_sum (fun (k : Fin (d+1)) hk => norm_nonneg (f.coeff k)) (Finset.mem_univ i)
    exact h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),norm_zero]
    exact polynomialLogSize_nonneg d f

theorem polynomialLogSize_add_le (d : ℕ) (f g : Polynomial ℂ) :
    polynomialLogSize d (f+g) ≤ polynomialLogSize d f+polynomialLogSize d g := by
  simp only [polynomialLogSize,Polynomial.coeff_add,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => norm_add_le _ _)

theorem polynomialLogSize_sub_le (d : ℕ) (f g : Polynomial ℂ) :
    polynomialLogSize d (f-g) ≤ polynomialLogSize d f+polynomialLogSize d g := by
  simp only [polynomialLogSize,Polynomial.coeff_sub,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => norm_sub_le _ _)

@[simp] theorem polynomialLogSize_smul (d : ℕ) (c : ℂ) (f : Polynomial ℂ) :
    polynomialLogSize d (c • f) = ‖c‖*polynomialLogSize d f := by
  simp only [polynomialLogSize,Polynomial.coeff_smul,smul_eq_mul,norm_mul,Finset.mul_sum]

@[simp] theorem polynomialLogSize_neg (d : ℕ) (f : Polynomial ℂ) :
    polynomialLogSize d (-f) = polynomialLogSize d f := by
  simp [polynomialLogSize]

theorem polynomialLogSize_sum_le {ι : Type*} (d : ℕ) (s : Finset ι) (f : ι → Polynomial ℂ) :
    polynomialLogSize d (∑ i ∈ s,f i) ≤ ∑ i ∈ s,polynomialLogSize d (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (polynomialLogSize_add_le d _ _).trans (add_le_add_left ih _)

/-- A deliberately generous but uniform bound for differentiation on degree ≤d. -/
theorem polynomialLogSize_derivative_le (d : ℕ) (f : Polynomial ℂ)
    (hf : f.natDegree ≤ d) :
    polynomialLogSize d f.derivative ≤ ((d : ℝ)+1)^2*polynomialLogSize d f := by
  have h (j : Fin (d+1)) : ‖f.derivative.coeff j‖ ≤ ((d : ℝ)+1)*polynomialLogSize d f := by
    rw [Polynomial.coeff_derivative,norm_mul,← Nat.cast_one (R := ℂ),← Nat.cast_add,Complex.norm_natCast]
    have hj : ((j.val+1 : ℕ) : ℝ) ≤ (d : ℝ)+1 := by exact_mod_cast (show j.val+1 ≤ d+1 by omega)
    exact (mul_le_mul (polynomialLogSize_coeff_le d f (j.val+1) hf) hj
      (Nat.cast_nonneg _) (polynomialLogSize_nonneg d f)).trans_eq (mul_comm _ _)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
  simpa only [polynomialLogSize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add,Nat.cast_one,pow_two,mul_assoc] using hs

theorem shiftedPolynomialDerivative_natDegree_le (c : ℂ) (f : Polynomial ℂ) :
    (shiftedPolynomialDerivative c f).natDegree ≤ f.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _))
    (Polynomial.natDegree_smul_le _ _))

theorem polynomialLogSize_shiftedDerivative_le (d : ℕ) (c : ℂ) (f : Polynomial ℂ)
    (hf : f.natDegree ≤ d) :
    polynomialLogSize d (shiftedPolynomialDerivative c f) ≤
      (((d : ℝ)+1)^2+‖c‖)*polynomialLogSize d f := by
  exact (polynomialLogSize_add_le d _ _).trans
    (by simp only [LinearMap.smul_apply,LinearMap.id_apply]; rw [polynomialLogSize_smul,add_mul]; exact add_le_add_right (polynomialLogSize_derivative_le d f hf) _)

/-- A lower estimate for the WHOLE first-order logarithmic operator. -/
theorem polynomialLogSize_shiftedDerivative_lower (d : ℕ) (c : ℂ) (f : Polynomial ℂ)
    (hf : f.natDegree ≤ d) :
    (‖c‖-((d : ℝ)+1)^2)*polynomialLogSize d f ≤
      polynomialLogSize d (shiftedPolynomialDerivative c f) := by
  have he : c • f = shiftedPolynomialDerivative c f-f.derivative := by
    rw [shiftedPolynomialDerivative_apply]; abel
  have h := polynomialLogSize_sub_le d (shiftedPolynomialDerivative c f) f.derivative
  rw [← he,polynomialLogSize_smul] at h
  have hd := polynomialLogSize_derivative_le d f hf
  nlinarith

end StrictEUnit
end
