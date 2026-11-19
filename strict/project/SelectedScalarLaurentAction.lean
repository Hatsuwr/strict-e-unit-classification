import LaurentOrdinaryDerivation
noncomputable section
namespace StrictEUnit

/-- Transparent spelling of the existing rational Laurent scalar action. -/
abbrev selectedLaurentRationalAct {K : Type*} [Field K]
    (c : RatFunc K) (y : LaurentSeries K) : LaurentSeries K := c • y

theorem selectedLaurentRationalAct_eq_smul {K : Type*} [Field K]
    (c : RatFunc K) (y : LaurentSeries K) :
    selectedLaurentRationalAct c y = c • y := rfl

end StrictEUnit
end
