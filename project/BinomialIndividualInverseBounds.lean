import BinomialConjugateBounds

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of one cleared nonzero pivot clears its inverse. This is
an INDIVIDUAL denominator certificate, not a common-prefix inverse bound. -/
theorem numberField_cleared_inverse_bound (x : K) (D : ℕ) (hD : 0<D)
    (hx : x≠0) (hi : IsIntegral ℤ ((D : K)*x)) :
    ∃ e : ℕ,0<e ∧ (e : ℝ)≤((D : ℝ)*NumberField.house x)^Module.finrank ℚ K ∧
      IsIntegral ℤ ((e : K)*x⁻¹) := by
  let v : 𝓞 K := ⟨(D : K)*x,hi⟩
  have hv : v≠0 := by
    intro h
    have he := congrArg (fun w : 𝓞 K => (w : K)) h
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hD)) hx he
  obtain ⟨he,heb,w,hw⟩ := ringOfIntegers_natAbs_norm_certificate v hv
  have hid : ((Int.natAbs (Algebra.norm ℤ v) : ℕ) : K)=(D : K)*x*(w : K) := by
    simpa only [map_natCast,map_mul] using congrArg (algebraMap (𝓞 K) K) hw
  refine ⟨Int.natAbs (Algebra.norm ℤ v),he,?_,?_⟩
  · apply heb.trans
    apply pow_le_pow_left₀ (NumberField.house_nonneg _)
    have h := NumberField.house_mul_le (D : K) x
    have hnat : NumberField.house (D : K)=(D : ℝ) := by
      simpa using (NumberField.house_intCast (K:=K) (D : ℤ))
    simpa only [hnat] using h
  · rw [hid]
    have heq : (D : K)*x*(w : K)*x⁻¹=(D : K)*(w : K) := by field_simp;ring
    rw [heq]
    exact (ordinaryJet_natCast_integral D).mul (NumberField.RingOfIntegers.isIntegral_coe w)

/-- Scalar products appearing on composite-filter diagonals. -/
def binomialCompositeValue {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (n : ℕ) : K :=
  ∏ i : Fin q,Ring.choose (rho (u i)+(n : K)) (ms i)

theorem binomialCompositeValue_house_bound {ι : Type*} [Fintype ι]
    (rho : ι → K) :
    ∃ H : ℝ,1≤H ∧ ∀ q N n,(n≤N) → ∀ (u : Fin q → ι) (ms : Fin q → ℕ),
      (∀ i,ms i≤N) → NumberField.house (binomialCompositeValue rho u ms n)≤H^(q*(N+1)) := by
  classical
  let H := 4*((∑ i : ι,NumberField.house (rho i))+1)
  have hsum : 0≤∑ i : ι,NumberField.house (rho i) := Finset.sum_nonneg (fun _ _ => NumberField.house_nonneg _)
  have hH : 1≤H := by dsimp [H];linarith
  refine ⟨H,hH,?_⟩
  intro q N n hn u ms hm
  have hfactor (i : Fin q) : NumberField.house (Ring.choose (rho (u i)+(n : K)) (ms i))≤H^(N+1) := by
    apply (numberField_choose_nat_translate_house_le _ _ _ _ (hm i) hn).trans
    apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (by have := NumberField.house_nonneg (rho (u i));linarith))
    have hi : NumberField.house (rho (u i))≤∑ v : ι,NumberField.house (rho v) :=
      Finset.single_le_sum (fun _ _ => NumberField.house_nonneg _) (Finset.mem_univ _)
    dsimp only [H]
    linarith
  calc
    NumberField.house (binomialCompositeValue rho u ms n) ≤
        ∏ i : Fin q,NumberField.house (Ring.choose (rho (u i)+(n : K)) (ms i)) := by
      unfold NumberField.house binomialCompositeValue
      rw [map_prod]
      exact Finset.norm_prod_le _ _
    _ ≤ ∏ _i : Fin q,H^(N+1) := Finset.prod_le_prod
      (fun i _ => NumberField.house_nonneg _) (fun i _ => hfactor i)
    _ = H^(q*(N+1)) := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul];congr 1;ring

/-- A single base works for every individual nonzero composite pivot. The
quantifiers deliberately leave e AFTER the pivot choice: no joint inverse
prefix estimate follows merely from these individual norm certificates. -/
theorem binomialCompositeValue_individual_inverse_bounds {ι : Type*} [Fintype ι]
    (rho : ι → K) (hrho : JointBinomialPrefixDenominators rho) (q : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N n,n≤N → ∀ (u : Fin q → ι) (ms : Fin q → ℕ),
      (∀ i,ms i≤N) → binomialCompositeValue rho u ms n≠0 →
      ∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧
        IsIntegral ℤ ((e : K)*(binomialCompositeValue rho u ms n)⁻¹) := by
  obtain ⟨B,hB,hden⟩ := hrho
  obtain ⟨H,hH,hhouse⟩ := binomialCompositeValue_house_bound rho
  refine ⟨(B*H)^(q*Module.finrank ℚ K),one_le_pow₀ (one_le_mul_of_one_le_of_one_le hB hH),?_⟩
  intro N n hn u ms hm hx
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  have hI : IsIntegral ℤ (((D^q : ℕ) : K)*binomialCompositeValue rho u ms n) := by
    have hfactor (i : Fin q) : IsIntegral ℤ ((D : K)*Ring.choose (rho (u i)+(n : K)) (ms i)) :=
      binomial_nat_translate_cleared _ _ N
        (by intro m hm;rw [field_choose_eq_descPochhammer_div];exact hDi m hm (u i)) n (ms i) (hm i)
    convert IsIntegral.prod (s:=Finset.univ) _ (fun i _ => hfactor i) using 1
    simp only [binomialCompositeValue,Nat.cast_pow,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  obtain ⟨e,he,heb,hei⟩ := numberField_cleared_inverse_bound _ (D^q) (pow_pos hD _) hx hI
  refine ⟨e,he,heb.trans ?_,hei⟩
  have hd : ((D^q : ℕ) : ℝ)≤B^(q*(N+1)) := by
    rw [Nat.cast_pow]
    calc
      (D : ℝ)^q≤(B^(N+1))^q := pow_le_pow_left₀ (Nat.cast_nonneg _) hDb q
      _ = B^(q*(N+1)) := by rw [← pow_mul];congr 1;ring
  calc
    (((D^q : ℕ) : ℝ)*NumberField.house (binomialCompositeValue rho u ms n))^Module.finrank ℚ K ≤
        (B^(q*(N+1))*H^(q*(N+1)))^Module.finrank ℚ K := by
      apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (NumberField.house_nonneg _))
      exact mul_le_mul hd (hhouse q N n hn u ms hm) (NumberField.house_nonneg _) (pow_nonneg (le_trans zero_le_one hB) _)
    _ = ((B*H)^(q*Module.finrank ℚ K))^(N+1) := by
      rw [← mul_pow,← pow_mul,← pow_mul]
      congr 1
      ring

end StrictEUnit
end
