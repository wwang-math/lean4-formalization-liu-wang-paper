import LiuWang.LiuWang2025SemilinearWaveAmplitudeJetOperators

/-!
# Focused tests for the jet-level wave and transport operators
-/

noncomputable section

open scoped BigOperators
open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveAmplitudeJetOperators

namespace LiuWangAmplitudeJetOperatorTests

variable {d : Nat}

/-- A source phase jet really is twice longitudinally differentiable data. -/
example {G : FermiMetricJet d} (P : SourcePhaseJet G) (a : Multiindex d)
    (s : Real) : HasDerivAt ((ofSourcePhase P).djet.c a)
      ((ofSourcePhase P).ddc a s) s :=
  (ofSourcePhase P).hasDerivAt_djet a s

/-- Convolution against a jet's own coefficients is the ordinary jet product. -/
example (u w : LongJet d) (a : Multiindex d) (s : Real) :
    convRaw u (fun b t => w.c b t) a s = (mul u w).c a s :=
  convRaw_mul u w a s

/-- The wave operator is local in transverse degree: degree `a` reads the
amplitude only through degree `deg a + 2`. -/
example (W : WaveJetData d) {u v : LongJet2 d} {a : Multiindex d} {s : Real}
    (hjet : ∀ b, deg b ≤ deg a + 2 -> u.jet.c b s = v.jet.c b s)
    (hdjet : ∀ b, deg b ≤ deg a + 1 -> u.djet.c b s = v.djet.c b s)
    (hddc : ∀ b, deg b ≤ deg a -> u.ddc b s = v.ddc b s) :
    W.jetBox u a s = W.jetBox v a s :=
  W.jetBox_congr hjet hdjet hddc

/-- At the centre the wave operator of the phase is `trace (C M) + beta^{i1}`,
agreeing with the existing `TransportCenterGeometry` formula. -/
example (W : WaveJetData d) (P : SourcePhaseJet W.G)
    (M : Real -> Fin d -> Fin d -> Complex) {s : Real}
    (hsymm : ∀ p q, M s p q = M s q p)
    (hphi2 : ∀ a : Multiindex d, deg a = 2 -> P.phi.c a s = quadCoeff (M s) a) :
    W.jetBox (ofSourcePhase P) 0 s
      = (∑ i, ∑ j, (2 * (W.G.Att i j).c 0 s) * M s i j)
        + (W.betaT W.G.i1).c 0 s :=
  W.jetBox_phase_deg_zero_trace P M hsymm hphi2

/-- The hierarchy expression carries the paper's sign convention. -/
example (W : WaveJetData d) (P : SourcePhaseJet W.G) (uk ukm : LongJet2 d)
    (a : Multiindex d) (s : Real) :
    W.jetHierarchy P uk ukm a s
      = -Complex.I * W.jetTransport P uk a s + W.jetBox ukm a s := rfl

#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.jetBox_congr
#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.continuous_jetBox
#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.continuous_jetTransport
#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.jetBox_phase_deg_zero
#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.hessian_at_center
#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.jetBox_phase_deg_zero_trace
#print axioms LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData.sum_eq_trace

end LiuWangAmplitudeJetOperatorTests
