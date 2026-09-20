import LiuWang.LiuWang2025SemilinearWaveChartBeamReflection
import LiuWang.LiuWang2025SemilinearWaveChartQuadraticPhase

/-! Focused regression file for the Section 3 local Gaussian-beam construction:
the chart WKB identity, the telescoped finite-order residual, the derived
profile bound and transverse `L^2` rate, the reflected jet, and the derived
reflected-boundary rate. -/

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamResidual
open LiuWang2025SemilinearWaveChartBeamProfile
open LiuWang2025SemilinearWaveChartBeamReflection

-- The chart jet carries genuine derivative data.
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet.waveOp
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet.eikonalSymbol
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet.transportTerm
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet.beam

-- The assembled WKB identity and its frequency specialization.
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet.waveOp_beam
#check @LiuWang2025SemilinearWaveChartWKB.ChartJet.waveOp_beam_freq

-- The truncated amplitude and the telescoped finite-order residual.
#check @LiuWang2025SemilinearWaveChartBeamResidual.truncatedAmplitude
#check @LiuWang2025SemilinearWaveChartBeamResidual.waveOp_combo
#check @LiuWang2025SemilinearWaveChartBeamResidual.transportTerm_combo
#check @LiuWang2025SemilinearWaveChartBeamResidual.waveOp_beam_eq_terminal

-- The derived profile bound and transverse rate.
#check @LiuWang2025SemilinearWaveChartBeamProfile.residual_radiusProfileBound
#check @LiuWang2025SemilinearWaveChartBeamProfile.residual_L2_rate

-- The reflection: chart instance, reflected jet, trace cancellation, rate.
#check @LiuWang2025SemilinearWaveChartBeamReflection.chartReflection
#check @LiuWang2025SemilinearWaveChartBeamReflection.chartReflection_normal_notMem_tangent
#check @LiuWang2025SemilinearWaveChartBeamReflection.ChartJet.compReflect
#check @LiuWang2025SemilinearWaveChartBeamReflection.reflectedDifferenceJet_eq_zero_on_face
#check @LiuWang2025SemilinearWaveChartBeamReflection.norm_exp_sub_exp_le
#check @LiuWang2025SemilinearWaveChartBeamReflection.expPhaseDifference_radiusProfileBound
#check @LiuWang2025SemilinearWaveChartBeamReflection.reflectedBoundary_L2_rate_of_phaseMatching

/-- The zero jet is a legitimate `ChartJet`, so the structure is inhabited and
the identities above are not vacuous. -/
def zeroJet (n : Nat) : ChartJet n where
  val := fun _ => 0
  d := fun _ _ => 0
  d2 := fun _ _ _ => 0
  hasDeriv := fun _ _ => hasDerivAt_const _ _
  hasDeriv2 := fun _ _ _ => hasDerivAt_const _ _

/-- A nonzero constant jet, to witness that `beam` is not identically zero. -/
def constJet (n : Nat) (c : Complex) : ChartJet n where
  val := fun _ => c
  d := fun _ _ => 0
  d2 := fun _ _ _ => 0
  hasDeriv := fun _ _ => hasDerivAt_const _ _
  hasDeriv2 := fun _ _ _ => hasDerivAt_const _ _

/-- The constant beam is the constant amplitude times a genuine exponential. -/
example (n : Nat) (w c : Complex) (phi : ChartJet n) (x : Fin n -> Real) :
    (beam w phi (constJet n c)).val x = c * Complex.exp (w * phi.val x) := rfl

/-- The reflected difference of a constant jet vanishes everywhere, and in
particular on the face; the cancellation theorem is consistent. -/
example (n : Nat) (i0 : Fin n) (c : Complex) (z : Fin n -> Real) :
    reflectedDifferenceJet i0 (constJet n c) z = 0 := by
  simp [reflectedDifferenceJet,
    LiuWang2025SemilinearWaveBoundaryReflection.BoundaryReflection.difference,
    LiuWang2025SemilinearWaveBoundaryReflection.BoundaryReflection.reflected,
    constJet]

/-- The reflecting face is nonempty, so the trace cancellation has content. -/
example (n : Nat) (i0 : Fin n) : (0 : Fin n -> Real) i0 = 0 := rfl

-- The constructed Riccati quadratic phase.
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet_d2
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet_im_coercive
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.constructedPhase_L2_rate

#print axioms LiuWang2025SemilinearWaveChartWKB.ChartJet.waveOp_beam
-- The constructed Riccati quadratic phase.
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet_d2
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet_im_coercive
#check @LiuWang2025SemilinearWaveChartQuadraticPhase.constructedPhase_L2_rate

#print axioms LiuWang2025SemilinearWaveChartWKB.ChartJet.waveOp_beam_freq
#print axioms LiuWang2025SemilinearWaveChartBeamResidual.waveOp_beam_eq_terminal
#print axioms LiuWang2025SemilinearWaveChartBeamProfile.residual_radiusProfileBound
#print axioms LiuWang2025SemilinearWaveChartBeamProfile.residual_L2_rate
#print axioms LiuWang2025SemilinearWaveChartBeamReflection.chartReflection
#print axioms LiuWang2025SemilinearWaveChartBeamReflection.ChartJet.compReflect
#print axioms LiuWang2025SemilinearWaveChartBeamReflection.reflectedDifferenceJet_eq_zero_on_face
#print axioms LiuWang2025SemilinearWaveChartBeamReflection.norm_exp_sub_exp_le
#print axioms LiuWang2025SemilinearWaveChartBeamReflection.expPhaseDifference_radiusProfileBound
#print axioms LiuWang2025SemilinearWaveChartBeamReflection.reflectedBoundary_L2_rate_of_phaseMatching

#print axioms LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet
#print axioms LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet_d2
#print axioms LiuWang2025SemilinearWaveChartQuadraticPhase.quadraticPhaseJet_im_coercive
#print axioms LiuWang2025SemilinearWaveChartQuadraticPhase.constructedPhase_L2_rate
