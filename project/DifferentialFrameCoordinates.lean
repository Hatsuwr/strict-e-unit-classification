import CoefficientEulerLeibniz

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {R : Type*} [CommRing R]

theorem differentialFrame_coordinates {r : ℕ} (D : R →+ R)
    (hD : ∀ x y,D (x*y)=D x*y+x*D y)
    (C B H J : Matrix (Fin r) (Fin r) R)
    (hJ : J*H=1) (hH : H*J=1)
    (hdH : (fun i j =>D (H i j))=C*H-H*B)
    (u : Fin r →R) (hu : (fun i =>D (u i))=C.mulVec u) :
    let v := J.mulVec u
    H.mulVec v=u ∧ (fun i =>D (v i))=B.mulVec v := by
  intro v
  have hv : H.mulVec v=u := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec,hH,Matrix.one_mulVec]
  have he : (fun i =>D (u i))=Matrix.mulVec (fun i j =>D (H i j)) v+
      H.mulVec (fun i =>D (v i)) := by
    rw [← hv]
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum,hD,Finset.sum_add_distrib,Pi.add_apply]
  rw [hu,hdH,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hv] at he
  have hc : H.mulVec (fun i =>D (v i))=H.mulVec (B.mulVec v) := by
    have hz : H.mulVec (fun i =>D (v i))-H.mulVec (B.mulVec v)=0 := by
      calc
        _=(C.mulVec u-H.mulVec (B.mulVec v)+H.mulVec (fun i =>D (v i)))-C.mulVec u := by abel
        _=0 := by rw [← he,sub_self]
    exact sub_eq_zero.mp hz
  refine ⟨hv,?_⟩
  have h := congrArg (fun w =>J.mulVec w) hc
  simpa only [Matrix.mulVec_mulVec,← Matrix.mul_assoc,hJ,Matrix.one_mul,Matrix.one_mulVec] using h

end StrictEUnit
end
