import LiuWang.LiuWang2025SemilinearWaveProductBoundaryPartialDN
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Liu--Wang measurable-boundary partial DN realization

The paper's partial data are measured on an accessible subset `Gamma` of the
lateral boundary, while the Green identity also contains the complementary
boundary contribution.  The product-boundary realization verifies the algebra
once a trace has already been split into two components.  This module constructs
that split from one genuine boundary `L2` trace.

For a boundary measure `mu` and a set `Gamma`, Mathlib supplies canonical
nonexpansive restriction maps

`L2(mu) -> L2(mu.restrict Gamma)` and
`L2(mu) -> L2(mu.restrict Gamma.compl)`.

Their product is the paper-facing boundary decomposition.  The two restrictions
jointly determine the original `L2` class, so no boundary information is lost or
invented by the product carrier.  A nonlinear accessible partial-DN equality can
then be differentiated three times and passed through the already verified
directed Green route to equation (4.3).

The remaining geometric/PDE inputs are the Lorentzian graph trace theorem, the
source-specific boundary measure and accessible set, and the Green formula for
the selected semilinear wave operator.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace LiuWang2025SemilinearWaveMeasurableBoundaryPartialDN

open LiuWang2025SemilinearWaveThirdOrderGreen
open LiuWang2025SemilinearWaveGeneratedThirdOrder
open LiuWang2025SemilinearWaveDirectedGreenRealization
open LiuWang2025SemilinearWaveGeneratedPartialDNMap
open LiuWang2025SemilinearWaveProductBoundaryPartialDN

variable {BoundaryPoint : Type*} [MeasurableSpace BoundaryPoint]

/-- Square-integrable complex normal traces on a measured boundary. -/
abbrev BoundaryL2 (mu : Measure BoundaryPoint) := Lp Complex 2 mu

/-- Canonical restriction of a full boundary trace to a boundary subset. -/
def boundaryRestriction
    (mu : Measure BoundaryPoint) (boundarySet : Set BoundaryPoint) :
    BoundaryL2 mu →L[Complex] BoundaryL2 (mu.restrict boundarySet) :=
  LpToLpRestrictCLM BoundaryPoint Complex Complex mu 2 boundarySet

/-- Restrict one full trace to the accessible set and its complement. -/
def boundarySplit
    (mu : Measure BoundaryPoint) (accessibleSet : Set BoundaryPoint) :
    BoundaryL2 mu →L[Complex]
      (BoundaryL2 (mu.restrict accessibleSet) ×
        BoundaryL2 (mu.restrict accessibleSet.compl)) :=
  (boundaryRestriction mu accessibleSet).prod
    (boundaryRestriction mu accessibleSet.compl)

@[simp] theorem boundarySplit_fst
    (mu : Measure BoundaryPoint) (accessibleSet : Set BoundaryPoint)
    (flux : BoundaryL2 mu) :
    (boundarySplit mu accessibleSet flux).1 =
      boundaryRestriction mu accessibleSet flux := rfl

@[simp] theorem boundarySplit_snd
    (mu : Measure BoundaryPoint) (accessibleSet : Set BoundaryPoint)
    (flux : BoundaryL2 mu) :
    (boundarySplit mu accessibleSet flux).2 =
      boundaryRestriction mu accessibleSet.compl flux := rfl

/-- Equality on the accessible set and its complement is equality of the full
boundary `L2` classes. -/
theorem eq_of_boundaryRestrictions_eq
    (mu : Measure BoundaryPoint) (accessibleSet : Set BoundaryPoint)
    (f g : BoundaryL2 mu)
    (haccessible : boundaryRestriction mu accessibleSet f =
      boundaryRestriction mu accessibleSet g)
    (hinaccessible : boundaryRestriction mu accessibleSet.compl f =
      boundaryRestriction mu accessibleSet.compl g) :
    f = g := by
  apply Lp.ext
  have haccessibleMaps :
      (boundaryRestriction mu accessibleSet f : BoundaryPoint → Complex) =ᵐ[
        mu.restrict accessibleSet]
      (boundaryRestriction mu accessibleSet g : BoundaryPoint → Complex) := by
    rw [haccessible]
  have haccessibleAE :
      (f : BoundaryPoint → Complex) =ᵐ[mu.restrict accessibleSet]
      (g : BoundaryPoint → Complex) :=
    (LpToLpRestrictCLM_coeFn Complex accessibleSet f).symm.trans
      (haccessibleMaps.trans
        (LpToLpRestrictCLM_coeFn Complex accessibleSet g))
  have hinaccessibleMaps :
      (boundaryRestriction mu accessibleSet.compl f : BoundaryPoint → Complex) =ᵐ[
        mu.restrict accessibleSet.compl]
      (boundaryRestriction mu accessibleSet.compl g : BoundaryPoint → Complex) := by
    rw [hinaccessible]
  have hinaccessibleAE :
      (f : BoundaryPoint → Complex) =ᵐ[mu.restrict accessibleSet.compl]
      (g : BoundaryPoint → Complex) :=
    (LpToLpRestrictCLM_coeFn Complex accessibleSet.compl f).symm.trans
      (hinaccessibleMaps.trans
        (LpToLpRestrictCLM_coeFn Complex accessibleSet.compl g))
  exact ae_of_ae_restrict_of_ae_restrict_compl accessibleSet
    haccessibleAE hinaccessibleAE

/-- The measurable boundary split is injective: its two coordinates are
restrictions of one trace rather than independent abstract data. -/
theorem boundarySplit_injective
    (mu : Measure BoundaryPoint) (accessibleSet : Set BoundaryPoint) :
    Function.Injective (boundarySplit mu accessibleSet) := by
  intro f g hsplit
  apply eq_of_boundaryRestrictions_eq mu accessibleSet f g
  · exact congrArg Prod.fst hsplit
  · exact congrArg Prod.snd hsplit

variable {Parameter State Residual Probe BackwardResidual BoundaryValue : Type*}

variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]
variable [CompleteSpace Parameter]
variable [NormedAddCommGroup State] [NormedSpace Complex State]
variable [CompleteSpace State]
variable [NormedAddCommGroup Residual] [NormedSpace Complex Residual]
variable [CompleteSpace Residual]
variable [AddCommGroup Probe] [Module Complex Probe]
variable [AddCommGroup BackwardResidual] [Module Complex BackwardResidual]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]

/-- Directed Green data with a single full `L2` normal trace.  The accessible
and inaccessible trace spaces and their restriction maps are generated from
`accessibleSet`. -/
structure MeasurableBoundaryGreenData
    (mu : Measure BoundaryPoint) (accessibleSet : Set BoundaryPoint) where
  forwardTimeSecond : State →ₗ[Complex] Residual
  forwardSpatial : State →ₗ[Complex] Residual
  forwardWave : State →ₗ[Complex] Residual
  backwardTimeSecond : Probe →ₗ[Complex] BackwardResidual
  backwardSpatial : Probe →ₗ[Complex] BackwardResidual
  backwardWave : Probe →ₗ[Complex] BackwardResidual
  bulkPairing : Residual →ₗ[Complex] Probe →ₗ[Complex] Complex
  adjointBulkPairing : State →ₗ[Complex] BackwardResidual →ₗ[Complex] Complex
  continuousNormalTrace : State →L[Complex] BoundaryL2 mu
  probeTrace : Probe →ₗ[Complex] BoundaryValue
  accessiblePairing :
    BoundaryL2 (mu.restrict accessibleSet) →ₗ[Complex]
      BoundaryValue →ₗ[Complex] Complex
  inaccessiblePairing :
    BoundaryL2 (mu.restrict accessibleSet.compl) →ₗ[Complex]
      BoundaryValue →ₗ[Complex] Complex
  forwardWave_decomposition :
    forwardWave = forwardTimeSecond - forwardSpatial
  backwardWave_decomposition :
    backwardWave = backwardTimeSecond - backwardSpatial
  timeIntegrationByParts : forall (u : State) (v : Probe),
    bulkPairing (forwardTimeSecond u) v =
      adjointBulkPairing u (backwardTimeSecond v)
  spatialGreenFormula : forall (u : State) (v : Probe),
    bulkPairing (forwardSpatial u) v -
        adjointBulkPairing u (backwardSpatial v) =
      accessiblePairing
          (boundaryRestriction mu accessibleSet (continuousNormalTrace u))
          (probeTrace v) +
        inaccessiblePairing
          (boundaryRestriction mu accessibleSet.compl (continuousNormalTrace u))
          (probeTrace v)

namespace MeasurableBoundaryGreenData

variable {mu : Measure BoundaryPoint}
variable {accessibleSet : Set BoundaryPoint}

/-- Convert the single-trace measurable-boundary data to the verified product
boundary engine. -/
def toProductBoundaryGreenData
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet) :
    ProductBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      (AccessibleFlux := BoundaryL2 (mu.restrict accessibleSet))
      (InaccessibleFlux := BoundaryL2 (mu.restrict accessibleSet.compl)) where
  forwardTimeSecond := D.forwardTimeSecond
  forwardSpatial := D.forwardSpatial
  forwardWave := D.forwardWave
  backwardTimeSecond := D.backwardTimeSecond
  backwardSpatial := D.backwardSpatial
  backwardWave := D.backwardWave
  bulkPairing := D.bulkPairing
  adjointBulkPairing := D.adjointBulkPairing
  continuousNormalTrace :=
    (boundarySplit mu accessibleSet).comp D.continuousNormalTrace
  probeTrace := D.probeTrace
  accessiblePairing := D.accessiblePairing
  inaccessiblePairing := D.inaccessiblePairing
  forwardWave_decomposition := D.forwardWave_decomposition
  backwardWave_decomposition := D.backwardWave_decomposition
  timeIntegrationByParts := D.timeIntegrationByParts
  spatialGreenFormula := by
    intro u v
    simpa using D.spatialGreenFormula u v

@[simp] theorem toProductBoundaryGreenData_normalTrace_fst
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (u : State) :
    (D.toProductBoundaryGreenData.continuousNormalTrace u).1 =
      boundaryRestriction mu accessibleSet (D.continuousNormalTrace u) := rfl

@[simp] theorem toProductBoundaryGreenData_normalTrace_snd
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (u : State) :
    (D.toProductBoundaryGreenData.continuousNormalTrace u).2 =
      boundaryRestriction mu accessibleSet.compl (D.continuousNormalTrace u) := rfl

variable {order : Nat}
variable
  {D : MeasurableBoundaryGreenData
    (State := State) (Residual := Residual) (Probe := Probe)
    (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
    mu accessibleSet}
variable
  {comparison : GeneratedCubicComparisonData
    (Parameter := Parameter)
    D.toProductBoundaryGreenData.toDirectedWaveGreenModel.toWaveGreenIdentityEngine
    order}

/-- Equality of the generated nonlinear accessible partial-DN maps. -/
def EventuallyEqualGeneratedPartialDNMaps
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (comparison : GeneratedCubicComparisonData
      (Parameter := Parameter)
      D.toProductBoundaryGreenData.toDirectedWaveGreenModel.toWaveGreenIdentityEngine
      order)
    (horder : 3 <= order) : Prop :=
  D.toProductBoundaryGreenData.EventuallyEqualGeneratedPartialDNMaps
    comparison horder

/-- Equality of nonlinear data gives equality of the third accessible normal
traces obtained by restricting the single full trace. -/
theorem generatedThirdAccessibleNormalTrace_eq
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (comparison : GeneratedCubicComparisonData
      (Parameter := Parameter)
      D.toProductBoundaryGreenData.toDirectedWaveGreenModel.toWaveGreenIdentityEngine
      order)
    (horder : 3 <= order)
    (hdata : D.EventuallyEqualGeneratedPartialDNMaps comparison horder)
    (direction : Fin 3 → Parameter) :
    boundaryRestriction mu accessibleSet
        (D.continuousNormalTrace (comparison.thirdVariation1 horder direction)) =
      boundaryRestriction mu accessibleSet
        (D.continuousNormalTrace
          (comparison.thirdVariation2 horder direction)) := by
  exact D.toProductBoundaryGreenData.generatedThirdAccessibleNormalTrace_eq
    comparison horder hdata direction

/-- End-to-end equation (4.3) with the inaccessible term realized as
restriction of the same full normal trace to the boundary complement. -/
theorem equation43_sourcePairing_eq_inaccessibleBoundary
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (comparison : GeneratedCubicComparisonData
      (Parameter := Parameter)
      D.toProductBoundaryGreenData.toDirectedWaveGreenModel.toWaveGreenIdentityEngine
      order)
    (horder : 3 <= order)
    (hdata : D.EventuallyEqualGeneratedPartialDNMaps comparison horder)
    (direction : Fin 3 → Parameter) (probe : Probe)
    (hprobe : D.backwardWave probe = 0) :
    D.bulkPairing
        (comparison.toThirdOrderWaveDifferenceData horder direction).coefficientDifferenceSource
        probe =
      D.inaccessiblePairing
        (boundaryRestriction mu accessibleSet.compl
          (D.continuousNormalTrace
            (comparison.toThirdOrderWaveDifferenceData horder direction).variationDifference))
        (D.probeTrace probe) := by
  exact D.toProductBoundaryGreenData
    |>.equation43_sourcePairing_eq_inaccessibleBoundary
      comparison horder hdata direction probe hprobe

/-- Measurable-boundary certificate: faithful boundary split, differentiated
accessible data, and the paper's equation (4.3). -/
structure Certificate
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (comparison : GeneratedCubicComparisonData
      (Parameter := Parameter)
      D.toProductBoundaryGreenData.toDirectedWaveGreenModel.toWaveGreenIdentityEngine
      order)
    (horder : 3 <= order)
    (hdata : D.EventuallyEqualGeneratedPartialDNMaps comparison horder)
    (direction : Fin 3 → Parameter) : Prop where
  boundarySplitFaithful : Function.Injective (boundarySplit mu accessibleSet)
  accessibleThirdTracesAgree :
    boundaryRestriction mu accessibleSet
        (D.continuousNormalTrace (comparison.thirdVariation1 horder direction)) =
      boundaryRestriction mu accessibleSet
        (D.continuousNormalTrace
          (comparison.thirdVariation2 horder direction))
  equation43 : forall probe, D.backwardWave probe = 0 →
    D.bulkPairing
        (comparison.toThirdOrderWaveDifferenceData horder direction).coefficientDifferenceSource
        probe =
      D.inaccessiblePairing
        (boundaryRestriction mu accessibleSet.compl
          (D.continuousNormalTrace
            (comparison.toThirdOrderWaveDifferenceData horder direction).variationDifference))
        (D.probeTrace probe)

def certificate
    (D : MeasurableBoundaryGreenData
      (State := State) (Residual := Residual) (Probe := Probe)
      (BackwardResidual := BackwardResidual) (BoundaryValue := BoundaryValue)
      mu accessibleSet)
    (comparison : GeneratedCubicComparisonData
      (Parameter := Parameter)
      D.toProductBoundaryGreenData.toDirectedWaveGreenModel.toWaveGreenIdentityEngine
      order)
    (horder : 3 <= order)
    (hdata : D.EventuallyEqualGeneratedPartialDNMaps comparison horder)
    (direction : Fin 3 → Parameter) :
    Certificate D comparison horder hdata direction where
  boundarySplitFaithful := boundarySplit_injective mu accessibleSet
  accessibleThirdTracesAgree :=
    D.generatedThirdAccessibleNormalTrace_eq comparison horder hdata direction
  equation43 :=
    D.equation43_sourcePairing_eq_inaccessibleBoundary
      comparison horder hdata direction

end MeasurableBoundaryGreenData

end LiuWang2025SemilinearWaveMeasurableBoundaryPartialDN
