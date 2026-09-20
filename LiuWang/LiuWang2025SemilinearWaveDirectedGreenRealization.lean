import LiuWang.LiuWang2025SemilinearWaveThirdOrderGreen
import Mathlib.Tactic.Abel

/-!
# Liu--Wang directed wave Green realization

This module refines the abstract Green engine used for equation (4.3) of
Liu--Wang, arXiv:2511.08794v1.  The forward carrier represents wave states
with zero lateral trace and zero initial Cauchy data.  The backward carrier
represents homogeneous adjoint waves with zero terminal Cauchy data.  Keeping
these carriers distinct prevents the initial and terminal conditions from
being silently identified.

The Lorentzian Green identity is not a field of the model.  It is derived
from three auditable inputs:

* the decomposition `Box_g = partial_t^2 - Delta_g` on both directed graph
  domains;
* time integration by parts between the zero-initial and zero-terminal
  carriers;
* the spatial Green formula carrying the lateral normal-trace term.

A second packet turns equality of differentiated partial DN traces on
`Gamma` into cancellation of the accessible boundary pairing.  Combining
the two constructions proves the exact source-to-inaccessible-boundary
identity in equation (4.3).  Concrete Sobolev graph spaces, Lorentzian trace
theorems, and the analytic integration-by-parts formulas are visible inputs
to this abstract model rather than hidden axioms.  The companion module
`LiuWang2025SemilinearWaveTemporalGreen` constructs the temporal input on a
weighted finite-mode core from the directed Cauchy endpoint conditions;
graph-norm closure and the concrete spatial Green/trace theorem remain open.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveDirectedGreenRealization

open Complex
open LiuWang2025SemilinearWaveThirdOrderGreen

variable {ForwardGraph BackwardGraph ForwardResidual BackwardResidual : Type*}
variable {BoundaryFlux BoundaryValue AccessibleFlux InaccessibleFlux : Type*}

variable [AddCommGroup ForwardGraph] [Module Complex ForwardGraph]
variable [AddCommGroup BackwardGraph] [Module Complex BackwardGraph]
variable [AddCommGroup ForwardResidual] [Module Complex ForwardResidual]
variable [AddCommGroup BackwardResidual] [Module Complex BackwardResidual]
variable [AddCommGroup BoundaryFlux] [Module Complex BoundaryFlux]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]
variable [AddCommGroup AccessibleFlux] [Module Complex AccessibleFlux]
variable [AddCommGroup InaccessibleFlux] [Module Complex InaccessibleFlux]

/-- Directed graph-domain realization of the wave operator and its formal
adjoint.  Endpoint and homogeneous lateral conditions are encoded by the
`ForwardGraph` and `BackwardGraph` carriers rather than repeated as unrelated
propositional side conditions. -/
structure DirectedWaveGreenModel where
  forwardTimeSecond : ForwardGraph →ₗ[Complex] ForwardResidual
  forwardSpatial : ForwardGraph →ₗ[Complex] ForwardResidual
  forwardWave : ForwardGraph →ₗ[Complex] ForwardResidual
  backwardTimeSecond : BackwardGraph →ₗ[Complex] BackwardResidual
  backwardSpatial : BackwardGraph →ₗ[Complex] BackwardResidual
  backwardWave : BackwardGraph →ₗ[Complex] BackwardResidual
  bulkPairing :
    ForwardResidual →ₗ[Complex] BackwardGraph →ₗ[Complex] Complex
  adjointBulkPairing :
    ForwardGraph →ₗ[Complex] BackwardResidual →ₗ[Complex] Complex
  normalTrace : ForwardGraph →ₗ[Complex] BoundaryFlux
  probeTrace : BackwardGraph →ₗ[Complex] BoundaryValue
  fullBoundaryPairing :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  forwardWave_decomposition :
    forwardWave = forwardTimeSecond - forwardSpatial
  backwardWave_decomposition :
    backwardWave = backwardTimeSecond - backwardSpatial
  timeIntegrationByParts : forall (u : ForwardGraph) (v : BackwardGraph),
    bulkPairing (forwardTimeSecond u) v =
      adjointBulkPairing u (backwardTimeSecond v)
  spatialGreenFormula : forall (u : ForwardGraph) (v : BackwardGraph),
    bulkPairing (forwardSpatial u) v -
        adjointBulkPairing u (backwardSpatial v) =
      fullBoundaryPairing (normalTrace u) (probeTrace v)

namespace DirectedWaveGreenModel

/-- A backward homogeneous wave balances its time and spatial pieces after
pairing against every forward graph state. -/
theorem backwardTimeSecond_pairing_eq_backwardSpatial_pairing
    (M : DirectedWaveGreenModel
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))
    (u : ForwardGraph) (v : BackwardGraph)
    (hv : M.backwardWave v = 0) :
    M.adjointBulkPairing u (M.backwardTimeSecond v) =
      M.adjointBulkPairing u (M.backwardSpatial v) := by
  have hvDecomposition :
      M.backwardTimeSecond v - M.backwardSpatial v = 0 := by
    simpa [M.backwardWave_decomposition] using hv
  have hpaired := congrArg
    (fun residual => M.adjointBulkPairing u residual) hvDecomposition
  exact sub_eq_zero.mp (by simpa using hpaired)

/-- The directed Lorentzian Green identity, derived from time integration by
parts, the spatial Green formula, and the backward wave equation. -/
theorem greenIdentity
    (M : DirectedWaveGreenModel
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))
    (u : ForwardGraph) (v : BackwardGraph)
    (hv : M.backwardWave v = 0) :
    -M.bulkPairing (M.forwardWave u) v =
      M.fullBoundaryPairing (M.normalTrace u) (M.probeTrace v) := by
  rw [M.forwardWave_decomposition, LinearMap.sub_apply, map_sub]
  calc
    -(M.bulkPairing (M.forwardTimeSecond u) v -
        M.bulkPairing (M.forwardSpatial u) v) =
        M.bulkPairing (M.forwardSpatial u) v -
          M.adjointBulkPairing u (M.backwardTimeSecond v) := by
      rw [M.timeIntegrationByParts]
      abel
    _ = M.bulkPairing (M.forwardSpatial u) v -
          M.adjointBulkPairing u (M.backwardSpatial v) := by
      rw [M.backwardTimeSecond_pairing_eq_backwardSpatial_pairing u v hv]
    _ = M.fullBoundaryPairing (M.normalTrace u) (M.probeTrace v) :=
      M.spatialGreenFormula u v

/-- Adapter to the source-ordered equation-(4.2)-to-(4.3) engine.  The two
`True` predicates record that zero lateral and zero initial conditions are
already enforced by the forward graph carrier. -/
def toWaveGreenIdentityEngine
    (M : DirectedWaveGreenModel
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)) :
    WaveGreenIdentityEngine
      (State := ForwardGraph) (Residual := ForwardResidual)
      (Probe := BackwardGraph) (BoundaryFlux := BoundaryFlux)
      (BoundaryValue := BoundaryValue) where
  wave := M.forwardWave
  normalTrace := M.normalTrace
  probeTrace := M.probeTrace
  bulkPairing := M.bulkPairing
  fullBoundaryPairing := M.fullBoundaryPairing
  homogeneousLateralTrace := fun _ => True
  zeroInitialCauchyData := fun _ => True
  backwardHomogeneousWave := fun v => M.backwardWave v = 0
  greenIdentity := by
    intro u v _ _ hv
    exact M.greenIdentity u v hv

end DirectedWaveGreenModel

section PartialDN

variable {Coefficient FirstVariation : Type*}
variable [AddCommGroup Coefficient] [Module Complex Coefficient]
variable [AddCommGroup FirstVariation] [Module Complex FirstVariation]

variable
  (M : DirectedWaveGreenModel
    (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
    (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))

variable
  (D : ThirdOrderWaveDifferenceData M.toWaveGreenIdentityEngine
    (Coefficient := Coefficient) (FirstVariation := FirstVariation))

/-- Source-faithful partial-DN trace data.  The equality field is the third
derivative of `Lambda_V1^Gamma = Lambda_V2^Gamma`; it is an equality of
restricted normal traces, not an already-cancelled scalar pairing. -/
structure DifferentiatedPartialDNTraceData where
  accessibleRestriction : BoundaryFlux →ₗ[Complex] AccessibleFlux
  inaccessibleRestriction : BoundaryFlux →ₗ[Complex] InaccessibleFlux
  accessiblePairing :
    AccessibleFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  inaccessiblePairing :
    InaccessibleFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  boundaryPairing_partition : forall flux trace,
    M.fullBoundaryPairing flux trace =
      accessiblePairing (accessibleRestriction flux) trace +
        inaccessiblePairing (inaccessibleRestriction flux) trace
  differentiatedPartialDNAgreement :
    accessibleRestriction (M.normalTrace D.thirdVariation1) =
      accessibleRestriction (M.normalTrace D.thirdVariation2)

namespace DifferentiatedPartialDNTraceData

variable
  {M : DirectedWaveGreenModel
    (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
    (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
  {D : ThirdOrderWaveDifferenceData M.toWaveGreenIdentityEngine
    (Coefficient := Coefficient) (FirstVariation := FirstVariation)}

/-- Accessible scalar pairing induced by restricting the normal trace to
`Gamma`. -/
def accessibleBoundaryPairing
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)) :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex :=
  P.accessiblePairing.comp P.accessibleRestriction

/-- Inaccessible scalar pairing induced by restricting the normal trace to
`Sigma \ Gamma`. -/
def inaccessibleBoundaryPairing
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)) :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex :=
  P.inaccessiblePairing.comp P.inaccessibleRestriction

/-- Differentiated equality of partial DN traces annihilates the accessible
normal trace of the third-variation difference. -/
theorem accessibleNormalVariationDifference_eq_zero
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)) :
    P.accessibleRestriction (M.normalTrace D.variationDifference) = 0 := by
  rw [ThirdOrderWaveDifferenceData.variationDifference, map_sub, map_sub,
    P.differentiatedPartialDNAgreement]
  simp

/-- The preceding trace equality gives the exact accessible-pairing
cancellation used after partitioning the lateral boundary. -/
theorem accessibleBoundaryPairing_variationDifference_eq_zero
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux))
    (probe : BackwardGraph) :
    P.accessibleBoundaryPairing
        (M.normalTrace D.variationDifference) (M.probeTrace probe) = 0 := by
  change P.accessiblePairing
    (P.accessibleRestriction (M.normalTrace D.variationDifference))
      (M.probeTrace probe) = 0
  rw [P.accessibleNormalVariationDifference_eq_zero]
  simp

/-- Construct the abstract partial-data packet from directed wave data and
the differentiated partial DN trace equality. -/
def toPartialDataGreenPacket
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux))
    (probe : BackwardGraph) (hprobe : M.backwardWave probe = 0) :
    PartialDataGreenPacket M.toWaveGreenIdentityEngine D where
  probe := probe
  variationDifference_homogeneousLateralTrace := trivial
  variationDifference_zeroInitialCauchyData := trivial
  probe_backwardHomogeneousWave := hprobe
  accessibleBoundaryPairing := P.accessibleBoundaryPairing
  inaccessibleBoundaryPairing := P.inaccessibleBoundaryPairing
  boundaryPartition := P.boundaryPairing_partition
  accessibleNormalAgreement :=
    P.accessibleBoundaryPairing_variationDifference_eq_zero probe

/-- Equation (4.3), now derived from the directed Green realization and
equality of differentiated partial DN traces on `Gamma`. -/
theorem equation43_sourcePairing_eq_inaccessibleBoundary
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux))
    (probe : BackwardGraph) (hprobe : M.backwardWave probe = 0) :
    M.bulkPairing D.coefficientDifferenceSource probe =
      P.inaccessiblePairing
        (P.inaccessibleRestriction (M.normalTrace D.variationDifference))
        (M.probeTrace probe) := by
  exact
    (P.toPartialDataGreenPacket probe hprobe).cubicSourcePairing_eq_inaccessibleBoundary

/-- One product certificate exposing the three conclusions a reviewer can
audit independently: Green's formula, accessible trace cancellation, and
the final equation-(4.3) identity. -/
structure Certificate
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux))
    (probe : BackwardGraph) (hprobe : M.backwardWave probe = 0) : Prop where
  directedGreenIdentity :
    -M.bulkPairing (M.forwardWave D.variationDifference) probe =
      M.fullBoundaryPairing
        (M.normalTrace D.variationDifference) (M.probeTrace probe)
  accessibleTraceDifferenceZero :
    P.accessibleRestriction (M.normalTrace D.variationDifference) = 0
  equation43 :
    M.bulkPairing D.coefficientDifferenceSource probe =
      P.inaccessiblePairing
        (P.inaccessibleRestriction (M.normalTrace D.variationDifference))
        (M.probeTrace probe)

def certificate
    (P : DifferentiatedPartialDNTraceData M D
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux))
    (probe : BackwardGraph) (hprobe : M.backwardWave probe = 0) :
    Certificate P probe hprobe where
  directedGreenIdentity := M.greenIdentity D.variationDifference probe hprobe
  accessibleTraceDifferenceZero :=
    P.accessibleNormalVariationDifference_eq_zero
  equation43 := P.equation43_sourcePairing_eq_inaccessibleBoundary probe hprobe

end DifferentiatedPartialDNTraceData

end PartialDN

end LiuWang2025SemilinearWaveDirectedGreenRealization
