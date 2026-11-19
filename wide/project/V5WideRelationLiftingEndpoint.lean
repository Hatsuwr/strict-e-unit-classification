import V5WideLinearLifting
import V5WideLiftingReduction

noncomputable section
namespace StrictEUnit

/-- Exact homogeneous polynomial specialization for wide E-functions in
an ordinary system, with the entire analytic functions as coordinates. -/
theorem v5_actual_wide_homogeneous_lifting :
    HomogeneousOrdinaryLiftingAtOne V5IsBroadEFunction :=
  v5_wide_homogeneous_lifting_of_linear v5_actual_wide_linear_lifting

/-- Exact polynomial lifting at one for the same finite family of wide
E-functions satisfying a Laurent system. No strict-growth assumption. -/
theorem v5_actual_wide_laurent_lifting : V5WideLaurentRelationLifting :=
  v5_wide_laurent_lifting_of_linear v5_actual_wide_linear_lifting

#print axioms v5_actual_wide_homogeneous_lifting
#print axioms v5_actual_wide_laurent_lifting
end StrictEUnit
