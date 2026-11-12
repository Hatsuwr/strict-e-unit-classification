import LaurentPolynomialCoefficientSwap
import DerivationTransport
import ScaledLaurentLogLeibniz

/-! Differential simplicity for the manuscript's actual abstract base presentation
k[t,t⁻¹][ell], with D(t)=t/N and D(ell)=1. No analytic identification is assumed. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]

@[simp] theorem laurentPolynomialSwap_symm_coeff
    (p : LaurentLogBase k) (j : ℕ) (n : ℤ) :
    (((laurentPolynomialSwap k).symm p) n).coeff j = (p.coeff j) n := by
  have h := laurentPolynomialSwap_coeff k ((laurentPolynomialSwap k).symm p) j n
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The manuscript's derivation on the exact polynomial presentation of its base. -/
def manuscriptBaseDerivation (N : ℕ) :
    Derivation k (LaurentLogBase k) (LaurentLogBase k) :=
  transportDerivation (laurentPolynomialSwap k) (scaledLaurentLogDerivation (N : k)⁻¹)

/-- Its actual two-index coefficient formula: formal log derivative plus
1/N times the Laurent Euler operator. -/
@[simp] theorem manuscriptBaseDerivation_coeff (N : ℕ)
    (p : LaurentLogBase k) (j : ℕ) (n : ℤ) :
    ((manuscriptBaseDerivation N p).coeff j) n =
      (p.coeff (j + 1)) n * (j + 1 : k) +
      ((N : k)⁻¹ * (n : k)) * (p.coeff j) n := by
  change ((transportDerivation (laurentPolynomialSwap k)
    (scaledLaurentLogDerivation (N : k)⁻¹) p).coeff j) n = _
  rw [transportDerivation_apply, laurentPolynomialSwap_coeff,
    scaledLaurentLogDerivation_apply, scaledLaurentLogD_coeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_derivative,
    Polynomial.coeff_smul, laurentPolynomialSwap_symm_coeff, smul_eq_mul]

/-- Full differential simplicity, with the manuscript scale and variable order,
from characteristic zero and N ≠ 0. -/
theorem manuscriptBase_stable_ideal_eq_top [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (I : Ideal (LaurentLogBase k))
    (hI : ∀ f ∈ I, manuscriptBaseDerivation N f ∈ I) (hI0 : I ≠ ⊥) : I = ⊤ := by
  apply stable_ideal_eq_top_transport (laurentPolynomialSwap k)
    (scaledLaurentLogDerivation (N : k)⁻¹) _ I hI hI0
  intro J hJ hJ0
  exact manuscriptLaurentLog_stable_ideal_eq_top N hN J hJ hJ0
end StrictEUnit
#print axioms StrictEUnit.laurentPolynomialSwap_symm_coeff
#print axioms StrictEUnit.manuscriptBaseDerivation
#print axioms StrictEUnit.manuscriptBaseDerivation_coeff
#print axioms StrictEUnit.manuscriptBase_stable_ideal_eq_top
