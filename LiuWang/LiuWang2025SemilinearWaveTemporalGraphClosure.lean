import LiuWang.LiuWang2025SemilinearWaveTemporalGreen

/-!
# Liu--Wang temporal Green graph-core closure

This module closes the weighted temporal Green identity from a smooth
finite-mode core to directed forward and backward graph carriers.  It is the
next analytic layer before the concrete Lorentzian realization used around
equation (4.3) of Liu--Wang, arXiv:2511.08794v1.

The closure data exposes four facts rather than hiding them in a finished
Green identity:

* forward core states converge together with their temporal operator;
* backward core states converge together with their temporal operator;
* the forward bulk pairing is jointly continuous;
* the backward bulk pairing is jointly continuous.

On the core, the equality is not supplied as a field.  Forward zero-initial
and backward zero-terminal weighted paths identify the two abstract pairings
with literal finite-mode spacetime integrals.  The theorem
`weightedTemporalGreen_finiteModes` proves their equality.  Joint continuity
and graph convergence then extend it to every directed graph state.

This verifies the graph-closure mechanism.  It does not construct the paper's
concrete Lorentzian Sobolev carriers, prove density of smooth waves in their
graph norms, or establish the spatial Green and normal-trace theorem.
-/

noncomputable section

open Filter Topology

namespace LiuWang2025SemilinearWaveTemporalGraphClosure

open LiuWang2025SemilinearWaveDirectedGreenRealization
open LiuWang2025SemilinearWaveTemporalGreen

variable {ForwardGraph BackwardGraph ForwardResidual BackwardResidual : Type*}
variable {BoundaryFlux BoundaryValue : Type*}

variable [NormedAddCommGroup ForwardGraph] [NormedSpace Complex ForwardGraph]
variable [NormedAddCommGroup BackwardGraph] [NormedSpace Complex BackwardGraph]
variable [NormedAddCommGroup ForwardResidual]
variable [NormedSpace Complex ForwardResidual]
variable [NormedAddCommGroup BackwardResidual]
variable [NormedSpace Complex BackwardResidual]
variable [AddCommGroup BoundaryFlux] [Module Complex BoundaryFlux]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]

/-- A finite weighted temporal core together with the exact graph convergence
and pairing continuity needed to close its identity.  The core types need no
ambient algebraic structure: all analytic information is carried by their
embeddings and weighted paths. -/
structure FiniteModeGraphCoreClosure {Mode ForwardCore BackwardCore : Type*}
    [DecidableEq Mode]
    (S : DirectedWaveGreenSkeleton
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))
    (modes : Finset Mode) (timeHorizon : Real)
    (density : Real -> Mode -> Complex) where
  forwardCoreEmbedding : ForwardCore -> ForwardGraph
  backwardCoreEmbedding : BackwardCore -> BackwardGraph

  forwardApproximation : forall u : ForwardGraph,
    exists sequence : Nat -> ForwardCore,
      Tendsto (fun n => forwardCoreEmbedding (sequence n)) atTop (nhds u) /\
      Tendsto
        (fun n => S.forwardTimeSecond (forwardCoreEmbedding (sequence n)))
        atTop (nhds (S.forwardTimeSecond u))
  backwardApproximation : forall v : BackwardGraph,
    exists sequence : Nat -> BackwardCore,
      Tendsto (fun n => backwardCoreEmbedding (sequence n)) atTop (nhds v) /\
      Tendsto
        (fun n => S.backwardTimeSecond (backwardCoreEmbedding (sequence n)))
        atTop (nhds (S.backwardTimeSecond v))

  bulkPairing_continuous : Continuous
    (fun pair : ForwardResidual × BackwardGraph =>
      S.bulkPairing pair.1 pair.2)
  adjointBulkPairing_continuous : Continuous
    (fun pair : ForwardGraph × BackwardResidual =>
      S.adjointBulkPairing pair.1 pair.2)

  forwardPath : ForwardCore ->
    ZeroInitialTemporalModePath modes timeHorizon density
  backwardPath : BackwardCore ->
    ZeroTerminalTemporalModePath modes timeHorizon density
  forwardTimePairing_eq : forall u v,
    S.bulkPairing
        (S.forwardTimeSecond (forwardCoreEmbedding u))
        (backwardCoreEmbedding v) =
      spacetimePairing modes timeHorizon
        (forwardPath u).toWeightedTemporalModePath.fluxDerivative
        (backwardPath v).toWeightedTemporalModePath.state
  backwardTimePairing_eq : forall u v,
    S.adjointBulkPairing
        (forwardCoreEmbedding u)
        (S.backwardTimeSecond (backwardCoreEmbedding v)) =
      spacetimePairing modes timeHorizon
        (forwardPath u).toWeightedTemporalModePath.state
        (backwardPath v).toWeightedTemporalModePath.fluxDerivative

namespace FiniteModeGraphCoreClosure

variable {Mode ForwardCore BackwardCore : Type*} [DecidableEq Mode]
variable
  {S : DirectedWaveGreenSkeleton
    (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
    (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
variable {modes : Finset Mode} {timeHorizon : Real}
variable {density : Real -> Mode -> Complex}

/-- The temporal identity on the embedded smooth core is generated from the
literal weighted finite-mode paths. -/
theorem core_timeIntegrationByParts
    (C : FiniteModeGraphCoreClosure S modes timeHorizon density
      (ForwardCore := ForwardCore) (BackwardCore := BackwardCore))
    (u : ForwardCore) (v : BackwardCore) :
    S.bulkPairing
        (S.forwardTimeSecond (C.forwardCoreEmbedding u))
        (C.backwardCoreEmbedding v) =
      S.adjointBulkPairing
        (C.forwardCoreEmbedding u)
        (S.backwardTimeSecond (C.backwardCoreEmbedding v)) := by
  rw [C.forwardTimePairing_eq, C.backwardTimePairing_eq]
  exact weightedTemporalGreen_finiteModes (C.forwardPath u) (C.backwardPath v)

/-- The finite-core temporal Green identity closes on all forward and backward
graph states.  Both the state and temporal operator converge, so this is
closure in the directed graph topology rather than only ambient-state
convergence. -/
theorem timeIntegrationByParts
    (C : FiniteModeGraphCoreClosure S modes timeHorizon density
      (ForwardCore := ForwardCore) (BackwardCore := BackwardCore))
    (u : ForwardGraph) (v : BackwardGraph) :
    S.bulkPairing (S.forwardTimeSecond u) v =
      S.adjointBulkPairing u (S.backwardTimeSecond v) := by
  obtain ⟨uSequence, huState, huTime⟩ := C.forwardApproximation u
  obtain ⟨vSequence, hvState, hvTime⟩ := C.backwardApproximation v
  have hleft : Tendsto
      (fun n => S.bulkPairing
        (S.forwardTimeSecond (C.forwardCoreEmbedding (uSequence n)))
        (C.backwardCoreEmbedding (vSequence n)))
      atTop
      (nhds (S.bulkPairing (S.forwardTimeSecond u) v)) := by
    exact C.bulkPairing_continuous.continuousAt.tendsto.comp
      (huTime.prodMk_nhds hvState)
  have hright : Tendsto
      (fun n => S.adjointBulkPairing
        (C.forwardCoreEmbedding (uSequence n))
        (S.backwardTimeSecond (C.backwardCoreEmbedding (vSequence n))))
      atTop
      (nhds (S.adjointBulkPairing u (S.backwardTimeSecond v))) := by
    exact C.adjointBulkPairing_continuous.continuousAt.tendsto.comp
      (huState.prodMk_nhds hvTime)
  have hsequence :
      (fun n => S.bulkPairing
        (S.forwardTimeSecond (C.forwardCoreEmbedding (uSequence n)))
        (C.backwardCoreEmbedding (vSequence n))) =
      (fun n => S.adjointBulkPairing
        (C.forwardCoreEmbedding (uSequence n))
        (S.backwardTimeSecond (C.backwardCoreEmbedding (vSequence n)))) := by
    funext n
    exact C.core_timeIntegrationByParts (uSequence n) (vSequence n)
  rw [hsequence] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Directed wave Green model whose temporal field is produced by finite-core
graph closure.  The spatial Green formula is still the separate source-facing
field of the skeleton. -/
def toDirectedWaveGreenModel
    (C : FiniteModeGraphCoreClosure S modes timeHorizon density
      (ForwardCore := ForwardCore) (BackwardCore := BackwardCore)) :
    DirectedWaveGreenModel
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue) where
  forwardTimeSecond := S.forwardTimeSecond
  forwardSpatial := S.forwardSpatial
  forwardWave := S.forwardWave
  backwardTimeSecond := S.backwardTimeSecond
  backwardSpatial := S.backwardSpatial
  backwardWave := S.backwardWave
  bulkPairing := S.bulkPairing
  adjointBulkPairing := S.adjointBulkPairing
  normalTrace := S.normalTrace
  probeTrace := S.probeTrace
  fullBoundaryPairing := S.fullBoundaryPairing
  forwardWave_decomposition := S.forwardWave_decomposition
  backwardWave_decomposition := S.backwardWave_decomposition
  timeIntegrationByParts := C.timeIntegrationByParts
  spatialGreenFormula := S.spatialGreenFormula

/-- The graph-closed model inherits the exact directed Green identity used in
equation (4.3). -/
theorem generated_greenIdentity
    (C : FiniteModeGraphCoreClosure S modes timeHorizon density
      (ForwardCore := ForwardCore) (BackwardCore := BackwardCore))
    (u : ForwardGraph) (v : BackwardGraph)
    (hv : S.backwardWave v = 0) :
    -S.bulkPairing (S.forwardWave u) v =
      S.fullBoundaryPairing (S.normalTrace u) (S.probeTrace v) := by
  exact C.toDirectedWaveGreenModel.greenIdentity u v hv

/-- One auditable certificate for the two conclusions contributed by this
module: graph-closed temporal integration by parts and the resulting directed
Green identity. -/
structure Certificate
    (C : FiniteModeGraphCoreClosure S modes timeHorizon density
      (ForwardCore := ForwardCore) (BackwardCore := BackwardCore))
    (u : ForwardGraph) (v : BackwardGraph)
    (hv : S.backwardWave v = 0) : Prop where
  temporalGreenClosed :
    S.bulkPairing (S.forwardTimeSecond u) v =
      S.adjointBulkPairing u (S.backwardTimeSecond v)
  directedGreenIdentity :
    -S.bulkPairing (S.forwardWave u) v =
      S.fullBoundaryPairing (S.normalTrace u) (S.probeTrace v)

def certificate
    (C : FiniteModeGraphCoreClosure S modes timeHorizon density
      (ForwardCore := ForwardCore) (BackwardCore := BackwardCore))
    (u : ForwardGraph) (v : BackwardGraph)
    (hv : S.backwardWave v = 0) : Certificate C u v hv where
  temporalGreenClosed := C.timeIntegrationByParts u v
  directedGreenIdentity := C.generated_greenIdentity u v hv

end FiniteModeGraphCoreClosure

end LiuWang2025SemilinearWaveTemporalGraphClosure
