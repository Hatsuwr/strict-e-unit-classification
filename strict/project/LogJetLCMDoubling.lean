import FallingLogJetArithmetic
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A prime power between n and 2*n produces a carry in the central binomial
coefficient. Uses mathlib's exact Kummer multiplicity formula. -/
theorem prime_dvd_central_choose_of_power_interval (p n a : ℕ) (hp : p.Prime)
    (ha : 0<a) (hn : n<p^a) (hu : p^a≤2*n) : p∣(2*n).choose n := by
  apply dvd_of_emultiplicity_pos
  rw [hp.emultiplicity_choose (by omega : n≤2*n) (Nat.lt_succ_self (Nat.log p (2*n)))]
  have he : a∈Finset.Ico 1 (Nat.log p (2*n)+1) :=
    Finset.mem_Ico.mpr ⟨ha,(Nat.le_log_of_pow_le hp.one_lt hu).trans_lt (Nat.lt_succ_self _)⟩
  have hcarry : p^a≤n%p^a+(2*n-n)%p^a := by
    rw [show 2*n-n=n by omega,Nat.mod_eq_of_lt hn]
    omega
  have hcard : 0<(Finset.filter (fun i => p^i≤n%p^i+(2*n-n)%p^i)
      (Finset.Ico 1 (Nat.log p (2*n)+1))).card :=
    Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨he,hcarry⟩⟩
  exact_mod_cast hcard

/-- Exact doubling divisibility. A new prime-power level costs at most one
prime, supplied by the central binomial coefficient. -/
theorem logJetLCM_doubling_dvd (n : ℕ) :
    logJetLCM (2*n)∣(2*n).choose n*logJetLCM n := by
  apply (logJetLCM_dvd_iff _ _).2
  intro k hk hkn
  have hc : 0<(2*n).choose n := Nat.choose_pos (by omega)
  apply (Nat.factorization_prime_le_iff_dvd (ne_of_gt hk)
    (ne_of_gt (Nat.mul_pos hc (logJetLCM_pos n)))).1
  intro p hp
  rw [Nat.factorization_mul (ne_of_gt hc) (ne_of_gt (logJetLCM_pos n)),Finsupp.add_apply]
  let a := k.factorization p
  have hpa : p^a≤k := Nat.le_of_dvd hk ((hp.pow_dvd_iff_le_factorization (ne_of_gt hk)).2 le_rfl)
  by_cases hlow : p^a≤n
  · have hf : a≤(logJetLCM n).factorization p :=
      (hp.pow_dvd_iff_le_factorization (ne_of_gt (logJetLCM_pos n))).1
        (logJetLCM_dvd n (p^a) (pow_pos hp.pos _) hlow)
    exact hf.trans (Nat.le_add_left _ _)
  · have hn : n<p^a := Nat.lt_of_not_ge hlow
    have hnpos : 0<n := by omega
    have ha : 0<a := by
      by_contra hz
      have ha0 : a=0 := by omega
      rw [ha0,pow_zero] at hn
      omega
    have he : p^a=p^(a-1)*p := by rw [← pow_succ];congr 1;omega
    have hprev : p^(a-1)≤n := by
      have hp2 := hp.two_le
      rw [he] at hpa
      nlinarith
    have hf : a-1≤(logJetLCM n).factorization p :=
      (hp.pow_dvd_iff_le_factorization (ne_of_gt (logJetLCM_pos n))).1
        (logJetLCM_dvd n (p^(a-1)) (pow_pos hp.pos _) hprev)
    have hchoose : 1≤((2*n).choose n).factorization p :=
      (hp.dvd_iff_one_le_factorization (ne_of_gt hc)).1
        (prime_dvd_central_choose_of_power_interval p n a hp ha hn (hpa.trans hkn))
    change a≤_
    omega

/-- Numerical version of the proved divisibility, retaining the exact LCM. -/
theorem logJetLCM_doubling_le (n : ℕ) :
    logJetLCM (2*n)≤(2*n).choose n*logJetLCM n :=
  Nat.le_of_dvd (Nat.mul_pos (Nat.choose_pos (by omega)) (logJetLCM_pos n))
    (logJetLCM_doubling_dvd n)

end StrictEUnit
end
