import LiuWang.LiuWang2025SemilinearWaveReflectedPhaseMismatch

open LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay
open LiuWang2025SemilinearWaveReflectedPhaseMismatch

#check norm_exp_sub_exp_le
#check norm_oscillatoryExp_sub_le_gaussian
#check norm_reflectedExp_le_gaussian
#check norm_reflectedBeamTrace_le_gaussian
#check Certificate
#check certificate

example
    {rho q phaseJetBound : Real}
    {incidentPhase reflectedPhase : Complex}
    (hrho : 0 ≤ rho)
    (hreflectedCoercive : q ≤ reflectedPhase.im)
    (hmismatchAbsorb : ‖incidentPhase - reflectedPhase‖ ≤ q / 2)
    (hmismatchJet : ‖incidentPhase - reflectedPhase‖ ≤ phaseJetBound) :
    ‖Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
        Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ ≤
      rho * phaseJetBound * Real.exp (-(rho * q) / 2) :=
  norm_oscillatoryExp_sub_le_gaussian hrho hreflectedCoercive
    hmismatchAbsorb hmismatchJet

#print axioms norm_oscillatoryExp_sub_le_gaussian
#print axioms norm_reflectedBeamTrace_le_gaussian
#print axioms certificate
