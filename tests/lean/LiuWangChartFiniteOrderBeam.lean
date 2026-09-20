import LiuWang.LiuWang2025SemilinearWaveChartBeamJetClosure
import LiuWang.LiuWang2025SemilinearWaveChartPhaseAnsatz

/-! Focused regression file for the finite-order Gaussian-beam construction:
the unconditional WKB expansion, the directional-jet Taylor remainder, the
transverse multi-index jet layer, the phase ansatz, and the equation-(3.11)
residual rate derived from the source's jet conditions. -/

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamAssembly
open LiuWang2025SemilinearWaveDirectionalJet
open LiuWang2025SemilinearWaveChartBeamFiniteOrder
open LiuWang2025SemilinearWaveChartBeamJetClosure
open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveChartPhaseAnsatz

-- The unconditional expansion and its specialization.
#check @LiuWang2025SemilinearWaveChartBeamAssembly.waveOp_beam_expand
#check @LiuWang2025SemilinearWaveChartBeamAssembly.waveOp_beam_eq_terminal_of_expand
#check @LiuWang2025SemilinearWaveChartBeamAssembly.hierarchyExpr

-- Finite directional jets and the Taylor remainder.
#check @LiuWang2025SemilinearWaveDirectionalJet.DirJet
#check @LiuWang2025SemilinearWaveDirectionalJet.DirJet.replicate_smul
#check @LiuWang2025SemilinearWaveDirectionalJet.DirJet.rayDeriv_hasDerivAt
#check @LiuWang2025SemilinearWaveDirectionalJet.norm_le_of_chain
#check @LiuWang2025SemilinearWaveDirectionalJet.taylor_remainder_bound
#check @LiuWang2025SemilinearWaveDirectionalJet.global_polynomial_bound_of_vanishing_jet

-- The finite-order residual and the source's exponent.
#check @LiuWang2025SemilinearWaveChartBeamFiniteOrder.waveOp_beam_split
#check @LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamRemainderPart_radiusProfileBound
#check @LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamTerminalPart_radiusProfileBound
#check @LiuWang2025SemilinearWaveChartBeamFiniteOrder.equation311_exponent_identity
#check @LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamRemainderPart_L2_equation311
#check @LiuWang2025SemilinearWaveChartBeamJetClosure.FiniteJetCondition
#check @LiuWang2025SemilinearWaveChartBeamJetClosure.polynomial_bound_of_finiteJetCondition
#check @LiuWang2025SemilinearWaveChartBeamJetClosure.beamRemainder_L2_equation311_of_finiteJets
#check @LiuWang2025SemilinearWaveChartBeamJetClosure.terminal_rate_le_equation311Rate

-- The multi-index transverse jet layer.
#check @LiuWang2025SemilinearWaveTransverseJet.jmul
#check @LiuWang2025SemilinearWaveTransverseJet.jmul_comm
#check @LiuWang2025SemilinearWaveTransverseJet.jderiv
#check @LiuWang2025SemilinearWaveTransverseJet.monomial_smul
#check @LiuWang2025SemilinearWaveTransverseJet.norm_monomial_le
#check @LiuWang2025SemilinearWaveTransverseJet.norm_realize_le_of_degree_ge

-- The phase ansatz.
#check @LiuWang2025SemilinearWaveChartPhaseAnsatz.linearJet
#check @LiuWang2025SemilinearWaveChartPhaseAnsatz.phaseAnsatz2
#check @LiuWang2025SemilinearWaveChartPhaseAnsatz.phaseAnsatz2_d2
#check @LiuWang2025SemilinearWaveChartPhaseAnsatz.phaseAnsatz2_im_coercive

/-- A genuinely non-constant finite directional jet: an affine coordinate
function, whose first directional derivative is the direction's coordinate and
whose higher derivatives vanish.  This witnesses that `DirJet` is not vacuous
and that its `hasDeriv` field is satisfiable. -/
def affineDirJet (n N : Nat) (i0 : Fin n) : DirJet n N where
  D := fun l x =>
    match l with
    | [] => ((x i0 : Real) : Complex)
    | [v] => ((v i0 : Real) : Complex)
    | _ :: _ :: _ => 0
  hasDeriv := by
    intro l _ v x
    match l with
    | [] =>
      have hbase := LiuWang2025SemilinearWaveChartQuadraticPhase.hasDerivAt_lineC
        (x i0) (v i0)
      refine hbase.congr_of_eventuallyEq ?_
      filter_upwards with t
      show (((x + t • v) i0 : Real) : Complex)
        = ((x i0 : Real) : Complex) + ((t : Real) : Complex) * ((v i0 : Real) : Complex)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
        Complex.ofReal_mul]
    | [w] => exact hasDerivAt_const _ _
    | _ :: _ :: _ => exact hasDerivAt_const _ _

/-- The example jet really is non-constant. -/
example (n N : Nat) (i0 : Fin n) (x : Fin n -> Real) :
    (affineDirJet n N i0).D [] x = ((x i0 : Real) : Complex) := rfl

/-- Its first directional derivative is the expected coordinate. -/
example (n N : Nat) (i0 : Fin n) (v x : Fin n -> Real) :
    (affineDirJet n N i0).D [v] x = ((v i0 : Real) : Complex) := rfl

/-- The zero jet satisfies the source's finite-order jet condition, so the
condition is satisfiable. -/
def zeroDirJet (n N : Nat) : DirJet n N where
  D := fun _ _ => 0
  hasDeriv := fun _ _ _ _ => hasDerivAt_const _ _

example (n N : Nat) (r : Real) :
    FiniteJetCondition (n := n) N (fun _ => 0) 0 r :=
  ⟨zeroDirJet n N, fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ => by simp [zeroDirJet], fun _ _ => rfl⟩

/-- Degree bookkeeping: the total degree of a multi-index really is the sum. -/
example (d : Nat) (a : Multiindex d) : deg a = ∑ i, a i := rfl

/-- The source's equation-(3.11) exponent at the source's own dimension and
Sobolev order zero. -/
example (N : Nat) :
    LiuWang2025SemilinearWaveEquation312EnergyClosure.equation311DecayExponent 3 N 0
      = ((N + 1 : Nat) : Real) / 2 + 3 / 4 - 0 - 2 := by
  unfold LiuWang2025SemilinearWaveEquation312EnergyClosure.equation311DecayExponent
  norm_num

#print axioms LiuWang2025SemilinearWaveChartBeamAssembly.waveOp_beam_expand
#print axioms LiuWang2025SemilinearWaveChartBeamAssembly.waveOp_beam_eq_terminal_of_expand
#print axioms LiuWang2025SemilinearWaveDirectionalJet.DirJet.replicate_smul
#print axioms LiuWang2025SemilinearWaveDirectionalJet.DirJet.rayDeriv_hasDerivAt
#print axioms LiuWang2025SemilinearWaveDirectionalJet.norm_le_of_chain
#print axioms LiuWang2025SemilinearWaveDirectionalJet.taylor_remainder_bound
#print axioms LiuWang2025SemilinearWaveDirectionalJet.global_polynomial_bound_of_vanishing_jet
#print axioms LiuWang2025SemilinearWaveChartBeamFiniteOrder.waveOp_beam_split
#print axioms LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamRemainderPart_radiusProfileBound
#print axioms LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamTerminalPart_radiusProfileBound
#print axioms LiuWang2025SemilinearWaveChartBeamFiniteOrder.equation311_exponent_identity
#print axioms LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamRemainderPart_L2_equation311
#print axioms LiuWang2025SemilinearWaveChartBeamJetClosure.polynomial_bound_of_finiteJetCondition
#print axioms LiuWang2025SemilinearWaveChartBeamJetClosure.beamRemainder_L2_equation311_of_finiteJets
#print axioms LiuWang2025SemilinearWaveChartBeamJetClosure.terminal_rate_le_equation311Rate
#print axioms LiuWang2025SemilinearWaveTransverseJet.jmul_comm
#print axioms LiuWang2025SemilinearWaveTransverseJet.monomial_smul
#print axioms LiuWang2025SemilinearWaveTransverseJet.norm_monomial_le
#print axioms LiuWang2025SemilinearWaveTransverseJet.norm_realize_le_of_degree_ge
#print axioms LiuWang2025SemilinearWaveChartPhaseAnsatz.linearJet
#print axioms LiuWang2025SemilinearWaveChartPhaseAnsatz.phaseAnsatz2_d2
#print axioms LiuWang2025SemilinearWaveChartPhaseAnsatz.phaseAnsatz2_im_coercive
