import LiuWang.LiuWang2025SemilinearWaveSpatialGreenCore

open MeasureTheory Set
open LiuWang2025SemilinearWaveSpatialGreenCore

#check @green_secondIdentity
#check @green_secondIdentity_tangentialMode
#check @lateralFlux_of_accessibleCancellation
#check @spacetimeGreenDefect_eq_lateralFlux
#check @spacetimeGreenDefect_eq_inaccessibleFlux
#check @certificate

/-- Green's second identity in the normal variable, with both faces kept. -/
example {u du ddu v dv ddv : ℝ → ℂ} {xMin xMax : ℝ}
    (hu : ∀ x ∈ uIcc xMin xMax, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ uIcc xMin xMax, HasDerivAt du (ddu x) x)
    (hv : ∀ x ∈ uIcc xMin xMax, HasDerivAt v (dv x) x)
    (hdv : ∀ x ∈ uIcc xMin xMax, HasDerivAt dv (ddv x) x)
    (hduInt : IntervalIntegrable du volume xMin xMax)
    (hdduInt : IntervalIntegrable ddu volume xMin xMax)
    (hdvInt : IntervalIntegrable dv volume xMin xMax)
    (hddvInt : IntervalIntegrable ddv volume xMin xMax) :
    (∫ x in xMin..xMax, ddu x * v x) - (∫ x in xMin..xMax, u x * ddv x)
      = (du xMax * v xMax - u xMax * dv xMax)
        - (du xMin * v xMin - u xMin * dv xMin) :=
  green_secondIdentity hu hdu hv hdv hduInt hdduInt hdvInt hddvInt

#print axioms green_secondIdentity
#print axioms green_secondIdentity_tangentialMode
#print axioms spacetimeGreenDefect_eq_lateralFlux
#print axioms spacetimeGreenDefect_eq_inaccessibleFlux
#print axioms certificate
