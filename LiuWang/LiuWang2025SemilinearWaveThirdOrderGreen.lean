import LiuWang.LiuWang2025SemilinearWaveLinearization
import Mathlib.Tactic.Abel

/-!
# Liu--Wang third-order wave equation and partial Green identity

This module formalizes the source-ordered bridge from equation (4.2) to
equation (4.3) in Liu--Wang, arXiv:2511.08794v1.

The two third variations solve wave equations whose sources are the cubic
coefficients applied to the same three first variations.  Linearity gives the
difference equation with source `(V3_1 - V3_2) w1 w2 w3`.  A reusable Green
identity engine then converts that source pairing into a boundary pairing.
Equality of the differentiated partial DN data cancels only the accessible
part, leaving exactly the inaccessible-boundary term used by the reflected
Gaussian-beam argument.

Concrete Lorentzian well-posedness, differentiability, traces, and Green's
formula remain explicit inputs to the engine; the algebraic composition and
partial-boundary bookkeeping are checked here without hidden axioms.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveThirdOrderGreen

open Complex

variable {Coefficient FirstVariation State Residual Probe : Type*}
variable {BoundaryFlux BoundaryValue : Type*}

variable [AddCommGroup Coefficient] [Module Complex Coefficient]
variable [AddCommGroup FirstVariation] [Module Complex FirstVariation]
variable [AddCommGroup State] [Module Complex State]
variable [AddCommGroup Residual] [Module Complex Residual]
variable [AddCommGroup Probe] [Module Complex Probe]
variable [AddCommGroup BoundaryFlux] [Module Complex BoundaryFlux]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]

/-- Multilinear realization of `(V3,w1,w2,w3) |-> V3 w1 w2 w3` in the
third differentiated wave equation. -/
abbrev CubicSourceMap :=
  Coefficient →ₗ[Complex]
    FirstVariation →ₗ[Complex]
      FirstVariation →ₗ[Complex]
        FirstVariation →ₗ[Complex] Residual

/-- Reusable abstract Green formula for the Lorentzian wave operator.  The
three predicates expose the lateral, initial, and backward-terminal
conditions under which the time-face terms vanish. -/
structure WaveGreenIdentityEngine where
  wave : State →ₗ[Complex] Residual
  normalTrace : State →ₗ[Complex] BoundaryFlux
  probeTrace : Probe →ₗ[Complex] BoundaryValue
  bulkPairing : Residual →ₗ[Complex] Probe →ₗ[Complex] Complex
  fullBoundaryPairing :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  homogeneousLateralTrace : State -> Prop
  zeroInitialCauchyData : State -> Prop
  backwardHomogeneousWave : Probe -> Prop
  greenIdentity : forall z w,
    homogeneousLateralTrace z ->
    zeroInitialCauchyData z ->
    backwardHomogeneousWave w ->
      -bulkPairing (wave z) w =
        fullBoundaryPairing (normalTrace z) (probeTrace w)

/-- The two source equations (4.2), sharing the same first variations but
having different cubic coefficients. -/
structure ThirdOrderWaveDifferenceData
    (G : WaveGreenIdentityEngine
      (State := State) (Residual := Residual) (Probe := Probe)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)) where
  cubicSource : CubicSourceMap
    (Coefficient := Coefficient) (FirstVariation := FirstVariation)
    (Residual := Residual)
  coefficient1 : Coefficient
  coefficient2 : Coefficient
  w1 : FirstVariation
  w2 : FirstVariation
  w3 : FirstVariation
  thirdVariation1 : State
  thirdVariation2 : State
  equation1 : G.wave thirdVariation1 =
    -cubicSource coefficient1 w1 w2 w3
  equation2 : G.wave thirdVariation2 =
    -cubicSource coefficient2 w1 w2 w3

namespace ThirdOrderWaveDifferenceData

variable
  {G : WaveGreenIdentityEngine
    (State := State) (Residual := Residual) (Probe := Probe)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}

/-- Difference of the two third variations. -/
def variationDifference
    (D : ThirdOrderWaveDifferenceData G
      (Coefficient := Coefficient) (FirstVariation := FirstVariation)) : State :=
  D.thirdVariation1 - D.thirdVariation2

/-- The coefficient-difference source in equation (4.2). -/
def coefficientDifferenceSource
    (D : ThirdOrderWaveDifferenceData G
      (Coefficient := Coefficient) (FirstVariation := FirstVariation)) : Residual :=
  D.cubicSource (D.coefficient1 - D.coefficient2) D.w1 D.w2 D.w3

/-- Multilinearity moves the coefficient difference inside the cubic source. -/
theorem coefficientDifferenceSource_eq_sub
    (D : ThirdOrderWaveDifferenceData G
      (Coefficient := Coefficient) (FirstVariation := FirstVariation)) :
    D.coefficientDifferenceSource =
      D.cubicSource D.coefficient1 D.w1 D.w2 D.w3 -
        D.cubicSource D.coefficient2 D.w1 D.w2 D.w3 := by
  simp [coefficientDifferenceSource]

/-- Checked difference equation:
`Box (U1_123 - U2_123) = -(V3_1 - V3_2) w1 w2 w3`. -/
theorem wave_variationDifference
    (D : ThirdOrderWaveDifferenceData G
      (Coefficient := Coefficient) (FirstVariation := FirstVariation)) :
    G.wave D.variationDifference = -D.coefficientDifferenceSource := by
  rw [variationDifference, map_sub, D.equation1, D.equation2,
    D.coefficientDifferenceSource_eq_sub]
  abel

end ThirdOrderWaveDifferenceData

/-- Partial-data packet for equation (4.3).  `accessibleNormalAgreement` is
the differentiated equality of the two DN maps on `Gamma`; the partition
field records `Sigma = Gamma union (Sigma \ Gamma)`. -/
structure PartialDataGreenPacket
    (G : WaveGreenIdentityEngine
      (State := State) (Residual := Residual) (Probe := Probe)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))
    (D : ThirdOrderWaveDifferenceData G
      (Coefficient := Coefficient) (FirstVariation := FirstVariation)) where
  probe : Probe
  variationDifference_homogeneousLateralTrace :
    G.homogeneousLateralTrace D.variationDifference
  variationDifference_zeroInitialCauchyData :
    G.zeroInitialCauchyData D.variationDifference
  probe_backwardHomogeneousWave : G.backwardHomogeneousWave probe
  accessibleBoundaryPairing :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  inaccessibleBoundaryPairing :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  boundaryPartition : forall flux trace,
    G.fullBoundaryPairing flux trace =
      accessibleBoundaryPairing flux trace +
        inaccessibleBoundaryPairing flux trace
  accessibleNormalAgreement :
    accessibleBoundaryPairing
      (G.normalTrace D.variationDifference) (G.probeTrace probe) = 0

namespace PartialDataGreenPacket

variable
  {G : WaveGreenIdentityEngine
    (State := State) (Residual := Residual) (Probe := Probe)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
  {D : ThirdOrderWaveDifferenceData G
    (Coefficient := Coefficient) (FirstVariation := FirstVariation)}

/-- Equation (4.3): the cubic coefficient-difference pairing equals the
inaccessible-boundary pairing after the accessible DN contribution cancels. -/
theorem cubicSourcePairing_eq_inaccessibleBoundary
    (P : PartialDataGreenPacket G D) :
    G.bulkPairing D.coefficientDifferenceSource P.probe =
      P.inaccessibleBoundaryPairing
        (G.normalTrace D.variationDifference) (G.probeTrace P.probe) := by
  calc
    G.bulkPairing D.coefficientDifferenceSource P.probe =
        -G.bulkPairing (G.wave D.variationDifference) P.probe := by
      rw [D.wave_variationDifference]
      simp
    _ = G.fullBoundaryPairing
          (G.normalTrace D.variationDifference) (G.probeTrace P.probe) :=
      G.greenIdentity D.variationDifference P.probe
        P.variationDifference_homogeneousLateralTrace
        P.variationDifference_zeroInitialCauchyData
        P.probe_backwardHomogeneousWave
    _ = P.accessibleBoundaryPairing
          (G.normalTrace D.variationDifference) (G.probeTrace P.probe) +
        P.inaccessibleBoundaryPairing
          (G.normalTrace D.variationDifference) (G.probeTrace P.probe) :=
      P.boundaryPartition _ _
    _ = P.inaccessibleBoundaryPairing
          (G.normalTrace D.variationDifference) (G.probeTrace P.probe) := by
      rw [P.accessibleNormalAgreement]
      simp

/-- Compact certificate carrying both the differentiated wave equation and
the source-to-inaccessible-boundary integral identity. -/
structure Certificate (P : PartialDataGreenPacket G D) : Prop where
  differentiatedWaveEquation :
    G.wave D.variationDifference = -D.coefficientDifferenceSource
  accessibleContributionZero :
    P.accessibleBoundaryPairing
      (G.normalTrace D.variationDifference) (G.probeTrace P.probe) = 0
  partialGreenIdentity :
    G.bulkPairing D.coefficientDifferenceSource P.probe =
      P.inaccessibleBoundaryPairing
        (G.normalTrace D.variationDifference) (G.probeTrace P.probe)

def certificate (P : PartialDataGreenPacket G D) : Certificate P where
  differentiatedWaveEquation := D.wave_variationDifference
  accessibleContributionZero := P.accessibleNormalAgreement
  partialGreenIdentity := P.cubicSourcePairing_eq_inaccessibleBoundary

end PartialDataGreenPacket

end LiuWang2025SemilinearWaveThirdOrderGreen
