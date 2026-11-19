import EntireTaylorEmbedding

/-! Genuine first-order analytic ODE nonvanishing. The formal uniqueness lemma is
proved coefficient by coefficient; it is not an assumed analytic uniqueness axiom. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A homogeneous first-order formal ODE with zero initial value has only the
zero solution, over a characteristic-zero field. -/
theorem powerSeries_firstOrder_zero {K : Type*} [Field K] [CharZero K]
    (f b : PowerSeries K)
    (hode : PowerSeries.derivative K f = b * f)
    (hzero : PowerSeries.constantCoeff K f = 0) : f = 0 := by
  have hc : ∀ n, PowerSeries.coeff K n f = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hzero
      | succ n =>
        have he := congrArg (PowerSeries.coeff K n) hode
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at he
        have hs : (∑ ij ∈ Finset.antidiagonal n,
            PowerSeries.coeff K ij.1 b * PowerSeries.coeff K ij.2 f) = 0 := by
          apply Finset.sum_eq_zero
          intro ij hij
          rw [ih ij.2 (by have hh := Finset.mem_antidiagonal.mp hij; omega), mul_zero]
        rw [hs] at he
        exact (mul_eq_zero.mp he).resolve_right (by exact_mod_cast Nat.succ_ne_zero n)
  ext n
  simpa only [map_zero] using hc n

/-- A nonvanishing leading coefficient gives the same formal uniqueness theorem
without an assumed divided differential equation. -/
theorem powerSeries_firstOrder_zero_of_regular {K : Type*} [Field K] [CharZero K]
    (p q f : PowerSeries K)
    (hp : PowerSeries.constantCoeff K p ≠ 0)
    (hode : p * PowerSeries.derivative K f = q * f)
    (hzero : PowerSeries.constantCoeff K f = 0) : f = 0 := by
  apply powerSeries_firstOrder_zero f (p⁻¹ * q) _ hzero
  calc
    PowerSeries.derivative K f = (p⁻¹ * p) * PowerSeries.derivative K f := by
      rw [PowerSeries.inv_mul_cancel p hp, one_mul]
    _ = p⁻¹ * (p * PowerSeries.derivative K f) := mul_assoc _ _ _
    _ = (p⁻¹ * q) * f := by rw [hode, mul_assoc]

/-- The actual derivative commutes with translation of an entire function. -/
theorem entire_deriv_translate {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    deriv (fun z => f (z+c)) = fun z => deriv f (z+c) := by
  funext z
  simpa using ((hf (z+c)).hasDerivAt.comp z ((hasDerivAt_id z).add_const c)).deriv

/-- A zero at an ordinary point of an actual entire homogeneous first-order
ODE forces the actual function to vanish on the whole plane. -/
theorem entire_firstOrder_zero_of_regular
    {p q f : ℂ → ℂ} (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hf : Differentiable ℂ f) (c : ℂ) (hpc : p c ≠ 0)
    (hode : ∀ z, p z * deriv f z = q z * f z) (hfc : f c = 0) :
    f = 0 := by
  let P : ℂ → ℂ := fun z => p (z+c)
  let Q : ℂ → ℂ := fun z => q (z+c)
  let F : ℂ → ℂ := fun z => f (z+c)
  have hP : Differentiable ℂ P := hp.comp (differentiable_id.add_const c)
  have hQ : Differentiable ℂ Q := hq.comp (differentiable_id.add_const c)
  have hF : Differentiable ℂ F := hf.comp (differentiable_id.add_const c)
  have hdF : Differentiable ℂ (deriv F) :=
    differentiableOn_univ.mp (hF.differentiableOn.deriv isOpen_univ)
  have hodeF : (fun z => P z * deriv F z) = fun z => Q z * F z := by
    funext z
    rw [show deriv F = fun z => deriv f (z+c) from entire_deriv_translate hf c]
    exact hode (z+c)
  have hseries : entireFormalTaylor F = 0 := by
    apply powerSeries_firstOrder_zero_of_regular
      (entireFormalTaylor P) (entireFormalTaylor Q) (entireFormalTaylor F)
    · simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        entireCauchyCoefficient_zero hP, P] using hpc
    · rw [← entireFormalTaylor_deriv hF, ← entireFormalTaylor_mul hP hdF,
        hodeF, entireFormalTaylor_mul hQ hF]
    · simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        entireCauchyCoefficient_zero hF, F] using hfc
  have hFzero : F = fun _ => 0 :=
    entireFormalTaylor_injective_on_entire hF (differentiable_const 0)
      (by simpa using hseries)
  funext z
  have hh := congrFun hFzero (z-c)
  simpa [F] using hh

/-- A single nonzero value forbids a zero at every ordinary point. The leading
coefficient may vanish elsewhere; no global inverse or primitive is assumed. -/
theorem entire_firstOrder_nonzero_at_regular
    {p q f : ℂ → ℂ} (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hf : Differentiable ℂ f)
    (hode : ∀ z, p z * deriv f z = q z * f z)
    {d : ℂ} (hd : f d ≠ 0) {c : ℂ} (hpc : p c ≠ 0) : f c ≠ 0 := by
  intro hfc
  have hzero := entire_firstOrder_zero_of_regular hp hq hf c hpc hode hfc
  exact hd (congrFun hzero d)

/-- Polynomial scalar ODE specialization, including an isolated possible
singularity at the origin and a nonzero normalization at one. -/
theorem entire_polynomial_firstOrder_nonzero_off_origin
    (p q : Polynomial ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hp : ∀ z : ℂ, z ≠ 0 → p.eval z ≠ 0)
    (hode : ∀ z, p.eval z * deriv f z = q.eval z * f z)
    (h1 : f 1 ≠ 0) : ∀ z, z ≠ 0 → f z ≠ 0 := by
  intro z hz
  exact entire_firstOrder_nonzero_at_regular p.differentiable q.differentiable
    hf hode h1 (hp z hz)

/-- An entire denominator-cleared ODE valid away from the origin also holds
at the origin, by continuity. -/
theorem entire_firstOrder_extend_across_origin
    {p q f : ℂ → ℂ} (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hf : Differentiable ℂ f)
    (hode : ∀ z, z ≠ 0 → p z * deriv f z = q z * f z) :
    ∀ z, p z * deriv f z = q z * f z := by
  have hdf : Differentiable ℂ (deriv f) :=
    differentiableOn_univ.mp (hf.differentiableOn.deriv isOpen_univ)
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (hp.continuous.mul hdf.continuous) (hq.continuous.mul hf.continuous)
    (fun z hz => hode z hz)
  exact congrFun heq

/-- A polynomial scalar equation only needs to be checked off the singular
origin, rather than postulating any differential identity there. -/
theorem entire_polynomial_firstOrder_nonzero_off_origin_of_punctured
    (p q : Polynomial ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hp : ∀ z : ℂ, z ≠ 0 → p.eval z ≠ 0)
    (hode : ∀ z, z ≠ 0 → p.eval z * deriv f z = q.eval z * f z)
    (h1 : f 1 ≠ 0) : ∀ z, z ≠ 0 → f z ≠ 0 :=
  entire_polynomial_firstOrder_nonzero_off_origin p q hf hp
    (entire_firstOrder_extend_across_origin p.differentiable q.differentiable hf hode) h1

end StrictEUnit
