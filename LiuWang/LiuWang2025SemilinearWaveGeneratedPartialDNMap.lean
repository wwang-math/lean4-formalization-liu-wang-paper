import LiuWang.LiuWang2025SemilinearWaveGeneratedThirdOrder
import LiuWang.LiuWang2025SemilinearWaveDirectedGreenRealization

/-!
# Liu--Wang generated partial DN map and equation (4.3)

The factorial implicit-function engine generates the two nonlinear solution
maps and their third variations.  The directed Green realization, however,
expects equality of the differentiated partial DN traces on the accessible
boundary.  This module derives that input from the paper's nonlinear data
hypothesis.

A `GeneratedPartialDNRealization` supplies a continuous accessible normal-trace
map and identifies it with restriction of the directed graph normal trace.
The two measured partial DN maps are its compositions with the generated
nonlinear solution maps.  If these measured maps agree near the zero datum,
Lean transports the eventual equality through every Frechet derivative.  At
order three, the continuous-linear composition rule identifies the result with
the accessible traces of the two generated third variations.  The existing
directed Green packet then yields equation (4.3).

Thus differentiated partial-DN agreement is a theorem, not a separate input.
Concrete Lorentzian graph spaces, trace boundedness, and identification of the
generated measured maps with the paper's partial DN maps remain source-facing
analytic work.
-/

noncomputable section

open Filter
open scoped Topology

namespace LiuWang2025SemilinearWaveGeneratedPartialDNMap

open LiuWang2025SemilinearWaveThirdOrderGreen
open LiuWang2025SemilinearWaveGeneratedThirdOrder
open LiuWang2025SemilinearWaveDirectedGreenRealization

variable {Parameter State Residual Probe BackwardResidual : Type*}
variable {BoundaryFlux BoundaryValue AccessibleFlux InaccessibleFlux : Type*}

variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]
variable [CompleteSpace Parameter]
variable [NormedAddCommGroup State] [NormedSpace Complex State]
variable [CompleteSpace State]
variable [NormedAddCommGroup Residual] [NormedSpace Complex Residual]
variable [CompleteSpace Residual]
variable [AddCommGroup Probe] [Module Complex Probe]
variable [AddCommGroup BackwardResidual] [Module Complex BackwardResidual]
variable [AddCommGroup BoundaryFlux] [Module Complex BoundaryFlux]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]
variable [NormedAddCommGroup AccessibleFlux] [NormedSpace Complex AccessibleFlux]
variable [CompleteSpace AccessibleFlux]
variable [AddCommGroup InaccessibleFlux] [Module Complex InaccessibleFlux]

variable
  {M : DirectedWaveGreenModel
    (ForwardGraph := State) (BackwardGraph := Probe)
    (ForwardResidual := Residual) (BackwardResidual := BackwardResidual)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
  {order : Nat}

/-- Paper-facing realization of the accessible partial DN observation.  The
continuous map is the object differentiated below; `accessibleNormalTrace_eq`
identifies it with the source-ordered restriction of the graph normal trace.
The remaining fields record the accessible/inaccessible partition consumed by
the already verified equation-(4.3) engine. -/
structure GeneratedPartialDNRealization
    (comparison : GeneratedCubicComparisonData
      (Parameter := Parameter) M.toWaveGreenIdentityEngine order) where
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
  accessibleNormalTrace : State →L[Complex] AccessibleFlux
  accessibleNormalTrace_eq : forall state,
    accessibleNormalTrace state =
      accessibleRestriction (M.normalTrace state)

namespace GeneratedPartialDNRealization

variable
  {comparison : GeneratedCubicComparisonData
    (Parameter := Parameter) M.toWaveGreenIdentityEngine order}

/-- First generated nonlinear partial DN map on the accessible boundary. -/
def generatedPartialDNMap1
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order) :
    Parameter -> AccessibleFlux :=
  R.accessibleNormalTrace ∘ comparison.factorialData1.solutionMap (by omega)

/-- Second generated nonlinear partial DN map on the accessible boundary. -/
def generatedPartialDNMap2
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order) :
    Parameter -> AccessibleFlux :=
  R.accessibleNormalTrace ∘ comparison.factorialData2.solutionMap (by omega)

/-- Equality of the two nonlinear partial DN maps on a neighborhood of the
zero boundary/source datum, matching the paper's inverse-data hypothesis. -/
def EventuallyEqualGeneratedPartialDNMaps
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order) : Prop :=
  R.generatedPartialDNMap1 horder =ᶠ[𝓝 (0 : Parameter)]
    R.generatedPartialDNMap2 horder

/-- The third derivative of the first generated partial DN map is the
accessible normal trace applied to the third generated solution variation. -/
theorem iteratedFDeriv_generatedPartialDNMap1
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order) :
    iteratedFDeriv Complex 3 (R.generatedPartialDNMap1 horder) 0 =
      R.accessibleNormalTrace.compContinuousMultilinearMap
        (iteratedFDeriv Complex 3
          (comparison.factorialData1.solutionMap (by omega)) 0) := by
  unfold generatedPartialDNMap1
  exact R.accessibleNormalTrace.iteratedFDeriv_comp_left
    (comparison.factorialData1.solutionMap_contDiffAt (by omega))
    (by exact_mod_cast horder)

/-- The analogous derivative identity for the second candidate. -/
theorem iteratedFDeriv_generatedPartialDNMap2
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order) :
    iteratedFDeriv Complex 3 (R.generatedPartialDNMap2 horder) 0 =
      R.accessibleNormalTrace.compContinuousMultilinearMap
        (iteratedFDeriv Complex 3
          (comparison.factorialData2.solutionMap (by omega)) 0) := by
  unfold generatedPartialDNMap2
  exact R.accessibleNormalTrace.iteratedFDeriv_comp_left
    (comparison.factorialData2.solutionMap_contDiffAt (by omega))
    (by exact_mod_cast horder)

/-- Neighborhood equality of the nonlinear partial DN maps implies equality
of every iterated Frechet derivative at the zero datum. -/
theorem iteratedFDeriv_generatedPartialDNMaps_eq
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order)
    (hdata : R.EventuallyEqualGeneratedPartialDNMaps horder) (n : Nat) :
    iteratedFDeriv Complex n (R.generatedPartialDNMap1 horder) 0 =
      iteratedFDeriv Complex n (R.generatedPartialDNMap2 horder) 0 := by
  have hderiv := Filter.EventuallyEq.iteratedFDeriv Complex hdata n
  exact hderiv.eq_of_nhds

/-- At order three, the preceding equality is exactly equality of the
accessible normal traces of the two generated third variations. -/
theorem generatedThirdAccessibleNormalTrace_eq
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order)
    (hdata : R.EventuallyEqualGeneratedPartialDNMaps horder)
    (direction : Fin 3 -> Parameter) :
    R.accessibleNormalTrace (comparison.thirdVariation1 horder direction) =
      R.accessibleNormalTrace
        (comparison.thirdVariation2 horder direction) := by
  have hderiv := congrArg (fun derivative => derivative direction)
    (R.iteratedFDeriv_generatedPartialDNMaps_eq horder hdata 3)
  rw [R.iteratedFDeriv_generatedPartialDNMap1 horder,
    R.iteratedFDeriv_generatedPartialDNMap2 horder] at hderiv
  simpa [GeneratedCubicComparisonData.thirdVariation1,
    GeneratedCubicComparisonData.thirdVariation2] using hderiv

/-- Equality of the nonlinear generated partial DN maps supplies the exact
`differentiatedPartialDNAgreement` field required by the directed Green
realization. -/
def toDifferentiatedPartialDNTraceData
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order)
    (hdata : R.EventuallyEqualGeneratedPartialDNMaps horder)
    (direction : Fin 3 -> Parameter) :
    DifferentiatedPartialDNTraceData M
      (comparison.toThirdOrderWaveDifferenceData horder direction)
      (AccessibleFlux := AccessibleFlux)
      (InaccessibleFlux := InaccessibleFlux) where
  accessibleRestriction := R.accessibleRestriction
  inaccessibleRestriction := R.inaccessibleRestriction
  accessiblePairing := R.accessiblePairing
  inaccessiblePairing := R.inaccessiblePairing
  boundaryPairing_partition := R.boundaryPairing_partition
  differentiatedPartialDNAgreement := by
    rw [← R.accessibleNormalTrace_eq, ← R.accessibleNormalTrace_eq]
    exact R.generatedThirdAccessibleNormalTrace_eq horder hdata direction

/-- End-to-end generated equation (4.3): equality of the nonlinear partial DN
maps near zero yields the cubic coefficient-difference pairing on the
inaccessible boundary for every homogeneous backward probe. -/
theorem equation43_sourcePairing_eq_inaccessibleBoundary_of_generatedPartialDN
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order)
    (hdata : R.EventuallyEqualGeneratedPartialDNMaps horder)
    (direction : Fin 3 -> Parameter) (probe : Probe)
    (hprobe : M.backwardWave probe = 0) :
    M.bulkPairing
        (comparison.toThirdOrderWaveDifferenceData horder direction).coefficientDifferenceSource
        probe =
      R.inaccessiblePairing
        (R.inaccessibleRestriction
          (M.normalTrace
            (comparison.toThirdOrderWaveDifferenceData horder direction).variationDifference))
        (M.probeTrace probe) := by
  exact (R.toDifferentiatedPartialDNTraceData horder hdata direction)
    |>.equation43_sourcePairing_eq_inaccessibleBoundary probe hprobe

/-- Auditable product certificate for nonlinear partial-DN equality, its
third derivative, accessible normal-trace cancellation, and equation (4.3). -/
structure Certificate
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order)
    (hdata : R.EventuallyEqualGeneratedPartialDNMaps horder)
    (direction : Fin 3 -> Parameter) : Prop where
  thirdMeasuredDerivativesAgree :
    iteratedFDeriv Complex 3 (R.generatedPartialDNMap1 horder) 0 =
      iteratedFDeriv Complex 3 (R.generatedPartialDNMap2 horder) 0
  accessibleThirdTracesAgree :
    R.accessibleRestriction
        (M.normalTrace (comparison.thirdVariation1 horder direction)) =
      R.accessibleRestriction
        (M.normalTrace (comparison.thirdVariation2 horder direction))
  equation43 : forall probe, M.backwardWave probe = 0 ->
    M.bulkPairing
        (comparison.toThirdOrderWaveDifferenceData horder direction).coefficientDifferenceSource
        probe =
      R.inaccessiblePairing
        (R.inaccessibleRestriction
          (M.normalTrace
            (comparison.toThirdOrderWaveDifferenceData horder direction).variationDifference))
        (M.probeTrace probe)

/-- The certificate is generated from eventual equality of the nonlinear
partial DN maps; differentiated trace equality is not separately assumed. -/
def certificate
    (R : GeneratedPartialDNRealization
      (AccessibleFlux := AccessibleFlux) (InaccessibleFlux := InaccessibleFlux)
      comparison)
    (horder : 3 <= order)
    (hdata : R.EventuallyEqualGeneratedPartialDNMaps horder)
    (direction : Fin 3 -> Parameter) :
    Certificate R horder hdata direction where
  thirdMeasuredDerivativesAgree :=
    R.iteratedFDeriv_generatedPartialDNMaps_eq horder hdata 3
  accessibleThirdTracesAgree := by
    rw [← R.accessibleNormalTrace_eq, ← R.accessibleNormalTrace_eq]
    exact R.generatedThirdAccessibleNormalTrace_eq horder hdata direction
  equation43 :=
    R.equation43_sourcePairing_eq_inaccessibleBoundary_of_generatedPartialDN
      horder hdata direction

end GeneratedPartialDNRealization

end LiuWang2025SemilinearWaveGeneratedPartialDNMap
