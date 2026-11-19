import WholeSystemMomentFrameTransport

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {R : Type*} [CommRing R]

/-- Source coordinates first, followed by moments in increasing degree. -/
def orderedMomentConnection {r s : ℕ} (C : Matrix (Fin r) (Fin r) R)
    (g : Fin r →R) (a : Fin (s+1) →R) : Matrix (Fin (r+(s+1))) (Fin (r+(s+1))) R :=
  Fin.addCases
    (fun i =>Fin.addCases (C i) (fun j =>if j.val=0 then g i else 0))
    (fun i =>Fin.addCases (fun _ =>0)
      (Fin.lastCases a (fun j =>fun k =>if k=j.succ then 1 else 0) i))

theorem orderedMomentConnection_cyclicShape {r s : ℕ} (C : Matrix (Fin r) (Fin r) R)
    (g : Fin r →R) (a : Fin (s+1) →R) (hC : EulerCyclicShape C)
    (hg0 : ∀ i,i.val+1<r →g i=0) (hg1 : ∀ i,i.val+1=r →IsUnit (g i)) :
    EulerCyclicShape (orderedMomentConnection C g a) := by
  constructor
  · intro i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        simpa only [orderedMomentConnection,Fin.addCases_left] using hC.1 i j hij
      | right j =>
        simp only [orderedMomentConnection,Fin.addCases_left,Fin.addCases_right]
        split_ifs with hj
        · apply hg0
          simp only [Fin.coe_castAdd,Fin.coe_natAdd] at hij
          omega
        · rfl
    | right i =>
      cases j using Fin.addCases with
      | left j =>simp [orderedMomentConnection]
      | right j =>
        simp only [Fin.coe_natAdd] at hij
        simp only [orderedMomentConnection,Fin.addCases_right]
        cases i using Fin.lastCases with
        | last =>simp only [Fin.val_last] at hij;omega
        | cast i =>
          simp only [Fin.lastCases_castSucc]
          apply if_neg
          intro he
          subst j
          simp at hij;omega
  · intro i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        simpa only [orderedMomentConnection,Fin.addCases_left] using hC.2 i j hij
      | right j =>
        simp only [Fin.coe_castAdd,Fin.coe_natAdd] at hij
        have hj : j.val=0 := by omega
        have hi : i.val+1=r := by omega
        simpa only [orderedMomentConnection,Fin.addCases_left,Fin.addCases_right,if_pos hj] using hg1 i hi
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        simp only [Fin.coe_castAdd,Fin.coe_natAdd] at hij
        omega
      | right j =>
        simp only [Fin.coe_natAdd] at hij
        simp only [orderedMomentConnection,Fin.addCases_right]
        cases i using Fin.lastCases with
        | last =>simp only [Fin.val_last] at hij;omega
        | cast i =>
          have hj : j=i.succ := Fin.ext (by simp only [Fin.val_succ];simp only [Fin.coe_castSucc] at hij;omega)
          simp [hj]

variable {K : Type*} [Field K] [CharZero K]

theorem sourceLaurentEulerBase_cyclicShape (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (M : ℕ) :
    EulerCyclicShape (sourceLaurentEulerBase n T U M) := by
  constructor
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>simp only [Fin.val_last] at hij;omega
    | cast i =>
      have h1 : j≠i.succ := by intro h;subst j;simp at hij
      have h2 : i.castSucc≠j := by intro h;subst j;simp at hij
      simp [sourceLaurentEulerBase,sameCompanionEulerPowerSeriesMatrix,
        Matrix.add_apply,Matrix.diagonal_apply,Pi.single_apply,h1,h1.symm,h2]
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>simp only [Fin.val_last] at hij;omega
    | cast i =>
      have hj : j=i.succ := Fin.ext hij
      subst j
      have h2 : i.castSucc≠i.succ := by intro h;have := congrArg Fin.val h;simp at this
      simp [sourceLaurentEulerBase,sameCompanionEulerPowerSeriesMatrix,
        Matrix.add_apply,Matrix.diagonal_apply,Pi.single_apply,h2]

/-- The ordered source-plus-moment connection is genuinely cyclic, for any
closing companion row. Its constructed frame exposes the actual splitting
condition rather than assuming it over the current coefficient field. -/
theorem orderedSourceMoment_constructed_frame (n s M : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (a : Fin (s+1) →PowerSeries K) :
    let C := orderedMomentConnection (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) a
    ∃ b : Fin (((n+1)+(s+1))+1) →PowerSeries K,
      b (Fin.last ((n+1)+(s+1)))=1 ∧
      ∀ hsplit : (scalarEulerCoefficientSymbol ((n+1)+(s+1))
        (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K),
      ∃ rho : Fin ((n+1)+(s+1)) →K,
      ∃ Y : Matrix (Fin ((n+1)+(s+1))) (Fin ((n+1)+(s+1))) (Polynomial (LaurentSeries K)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) := by
  intro C
  have hC : EulerCyclicShape C := by
    apply orderedMomentConnection_cyclicShape
    · exact sourceLaurentEulerBase_cyclicShape n T U M
    · intro i hi;rw [augmentedSourceEulerColumn,if_neg (by omega)]
    · exact augmentedSourceEulerColumn_unit n T hT
  obtain ⟨b,G,H,hb,hdet,hGH,hHG,hconn⟩ := cyclicShape_exists_scalarGauge C (by omega) hC
  refine ⟨b,hb,fun hsplit =>?_⟩
  have htop : PowerSeries.constantCoeff K (b (Fin.last ((n+1)+(s+1))))≠0 := by
    rw [hb,map_one];exact one_ne_zero
  exact regularScalarGauge_constructed_log_frame C b G H htop hGH hHG hconn hsplit

end StrictEUnit
end
