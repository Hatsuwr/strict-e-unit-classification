import V5BroadConjugation
import V5BroadAlgebraicProduct

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The binomial convolution exactly corresponds to multiplication of literal
formal factorial series. -/
theorem v5_factorial_series_binomialConvolution {K : Type*} [Field K] [CharZero K]
    (a b : ℕ → K) :
    PowerSeries.mk (fun n => v5BinomialConvolution a b n / (n.factorial : K)) =
      PowerSeries.mk (fun n => a n / (n.factorial : K)) *
      PowerSeries.mk (fun n => b n / (n.factorial : K)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk,v5BinomialConvolution,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfac : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Nat.cast_choose K hkn]
  calc
    _ = ((n.factorial : K)/(n.factorial : K)) *
      ((a k/(k.factorial : K))*(b (n-k)/((n-k).factorial : K))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by rw [div_self hfac, one_mul]

theorem v5_factorial_series_cauchyCoefficient (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (n : ℕ) :
    entireCauchyCoefficient f n = (a n : ℂ)/(n.factorial : ℂ) := by
  apply entireCauchyCoefficient_eq_of_hasSum hf
  intro z
  convert hs z using 1
  funext j
  ring

/-- The existing subfield-Taylor algebra contains any entire factorial series
with algebraic coefficients; no strict growth is needed. -/
def v5FactorialEntire (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z)) :
    subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
  ⟨⟨f,hf⟩, (mem_subfieldEntireFunctionAlgebra _ _).mpr (fun n => by
    change entireCauchyCoefficient f n ∈ (algebraicClosure ℚ ℂ).toSubfield
    rw [v5_factorial_series_cauchyCoefficient f hf a hs]
    exact (algebraicClosure ℚ ℂ).toSubfield.div_mem (a n).property (natCast_mem _ _))⟩

theorem v5_factorialEntire_taylor (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z)) :
    subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield (v5FactorialEntire f hf a hs) =
      PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex)) := by
  apply PowerSeries.ext
  intro n
  apply Subtype.ext
  simpa [subfieldEntireTaylorAlgHom, subfieldEntireTaylorSeries, v5FactorialEntire]
    using v5_factorial_series_cauchyCoefficient f hf a hs n

theorem v5_broad_actual_mul_with_coefficients {f g : ℂ → ℂ}
    (a b : ℕ → AlgebraicComplex)
    (hdf : Differentiable ℂ f) (hdg : Differentiable ℂ g)
    (hsf : ∀ z : ℂ, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (hsg : ∀ z : ℂ, HasSum (fun n => (b n : ℂ)*z^n/(n.factorial : ℂ)) (g z))
    (hof : HasAlgebraicPolynomialODE f) (hog : HasAlgebraicPolynomialODE g)
    (ha : V5BroadAlgebraicArithmetic a) (hb : V5BroadAlgebraicArithmetic b) :
    (∀ z, HasSum (fun n => ((v5BinomialConvolution a b n : AlgebraicComplex) : ℂ)*
      z^n/(n.factorial : ℂ)) (f z*g z)) ∧
    V5IsBroadEFunction (fun z => f z * g z) := by
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let F := v5FactorialEntire f hdf a hsf
  let G := v5FactorialEntire g hdg b hsg
  have hmul : HasAlgebraicPolynomialODE (fun z => f z*g z) :=
    (stage14_algebraicPolynomialODE_iff_subfield _).mpr
      (stage14_actualSubfieldODE_mul k F G hof hog)
  have H : subfieldEntireTaylorAlgHom k (F*G) =
      PowerSeries.mk (fun n => v5BinomialConvolution a b n / (n.factorial : AlgebraicComplex)) := by
    rw [map_mul, v5_factorial_series_binomialConvolution]
    congr 1
    · exact v5_factorialEntire_taylor f hdf a hsf
    · exact v5_factorialEntire_taylor g hdg b hsg
  have hcoef (n : ℕ) : entireCauchyCoefficient (fun z => f z*g z) n =
      ((v5BinomialConvolution a b n : AlgebraicComplex) : ℂ)/(n.factorial : ℂ) := by
    have hn := congrArg (fun x : PowerSeries AlgebraicComplex =>
      ((PowerSeries.coeff AlgebraicComplex n x : AlgebraicComplex) : ℂ)) H
    simpa [subfieldEntireTaylorAlgHom,subfieldEntireTaylorSeries] using hn
  have hsum (z : ℂ) : HasSum (fun n => ((v5BinomialConvolution a b n : AlgebraicComplex) : ℂ)*
      z^n/(n.factorial : ℂ)) (f z*g z) := by
    have h := entireCauchyCoefficient_hasSum (hdf.mul hdg) z
    simp_rw [hcoef] at h
    convert h using 1
    funext j
    ring
  exact ⟨hsum,⟨v5BinomialConvolution a b,hdf.mul hdg,hsum,hmul,
    v5_broad_algebraicArithmetic_binomialConvolution a b ha hb⟩⟩

theorem v5_broad_actual_mul {f g : ℂ → ℂ} (hf : V5IsBroadEFunction f) (hg : V5IsBroadEFunction g) :
    V5IsBroadEFunction (fun z => f z*g z) := by
  obtain ⟨a,hdf,hsf,hof,ha⟩ := hf
  obtain ⟨b,hdg,hsg,hog,hb⟩ := hg
  exact (v5_broad_actual_mul_with_coefficients a b hdf hdg hsf hsg hof hog ha hb).2

#print axioms v5_factorial_series_binomialConvolution
#print axioms v5_factorialEntire_taylor
#print axioms v5_broad_actual_mul_with_coefficients
#print axioms v5_broad_actual_mul
end StrictEUnit
end
