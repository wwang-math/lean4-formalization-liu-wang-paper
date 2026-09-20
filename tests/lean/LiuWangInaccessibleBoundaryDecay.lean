import LiuWang.LiuWang2025SemilinearWaveInaccessibleBoundaryDecay

open Filter Topology
open LiuWang2025SemilinearWaveInaccessibleBoundaryDecay

#check @norm_beamExponential
#check @norm_beamExponential_le
#check @norm_beamTrace_le
#check @tendsto_natPow_mul_exp_neg
#check @InaccessibleTraceData.sobolevEnvelope_tendsto_zero
#check @InaccessibleTraceData.weighted_sobolevEnvelope_tendsto_zero
#check @GaussianFarBoundaryPointRecovery.coefficient_eq_zero

/-- The exact Gaussian modulus of the beam's oscillatory factor. -/
example (rho : ℝ) (phi : ℂ) :
    ‖Complex.exp (Complex.I * (rho : ℂ) * phi)‖ = Real.exp (-(rho * phi.im)) :=
  norm_beamExponential rho phi

/-- The inaccessible boundary Sobolev envelope decays faster than every
polynomial rate. -/
example {Index E : Type} [Fintype Index] [SeminormedAddCommGroup E]
    (D : InaccessibleTraceData Index E) (M : ℕ) :
    Tendsto (fun rho : ℕ => (rho : ℝ) ^ M * D.sobolevEnvelope rho) atTop (nhds 0) :=
  D.weighted_sobolevEnvelope_tendsto_zero M

/-- Point recovery with the inaccessible-boundary limit generated. -/
example {Index : Type} [Fintype Index]
    (D : GaussianFarBoundaryPointRecovery Index) : D.coefficient = 0 :=
  D.coefficient_eq_zero

#print axioms norm_beamExponential
#print axioms norm_beamTrace_le
#print axioms tendsto_natPow_mul_exp_neg
#print axioms InaccessibleTraceData.weighted_sobolevEnvelope_tendsto_zero
#print axioms GaussianFarBoundaryPointRecovery.coefficient_eq_zero
