import LiuWang.LiuWang2025SemilinearWaveMinkowskiFourNull
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Liu--Wang 2025: coordinate transport of the Minkowski four-null witness

The standard Minkowski benchmark constructs the local four-null interaction in
one fixed `1 + 2` coordinate model.  This file proves that the whole
certificate is invariant under a continuous linear change of tangent
coordinates.  The inverse metric, Lorentz frame, four covectors, signed
balance, and affine phase first jets are transported together rather than
reintroduced as independent assumptions.

The remaining paper-facing geometric input is now precise: a local coordinate
equivalence at the selected interaction point must identify the actual
Lorentzian inverse metric and time orientation with this transported normal
form.  Global broken-null-geodesic reachability, boundary transversality, and
reflected Gaussian-beam higher jets are not claimed here.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveTransportedMinkowskiFourNull

open LiuWang2025SemilinearWaveFourNullCovectors
open LiuWang2025SemilinearWavePhaseBalance

namespace Standard

abbrev Tangent := LiuWang2025SemilinearWaveMinkowskiFourNull.Tangent

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace Real Y]

/-- Pull a standard covector back through target-to-standard coordinates. -/
def pullbackCovector (coordinates : Y ≃L[Real] Tangent) :
    (Tangent →L[Real] Real) →L[Real] (Y →L[Real] Real) :=
  (ContinuousLinearMap.compL Real Y Tangent Real).flip
    coordinates.toContinuousLinearMap

/-- Express a target covector in the standard coordinate model. -/
def covectorInStandardCoordinates (coordinates : Y ≃L[Real] Tangent) :
    (Y →L[Real] Real) →L[Real] (Tangent →L[Real] Real) :=
  (ContinuousLinearMap.compL Real Tangent Y Real).flip
    coordinates.symm.toContinuousLinearMap

@[simp] theorem pullbackCovector_apply
    (coordinates : Y ≃L[Real] Tangent)
    (xi : Tangent →L[Real] Real) (y : Y) :
    pullbackCovector coordinates xi y = xi (coordinates y) := rfl

@[simp] theorem covectorInStandardCoordinates_apply
    (coordinates : Y ≃L[Real] Tangent)
    (eta : Y →L[Real] Real) (x : Tangent) :
    covectorInStandardCoordinates coordinates eta x =
      eta (coordinates.symm x) := rfl

@[simp] theorem covectorInStandardCoordinates_pullback
    (coordinates : Y ≃L[Real] Tangent)
    (xi : Tangent →L[Real] Real) :
    covectorInStandardCoordinates coordinates
        (pullbackCovector coordinates xi) = xi := by
  ext x
  simp

@[simp] theorem pullback_covectorInStandardCoordinates
    (coordinates : Y ≃L[Real] Tangent)
    (eta : Y →L[Real] Real) :
    pullbackCovector coordinates
        (covectorInStandardCoordinates coordinates eta) = eta := by
  ext y
  simp

/-- The standard inverse Minkowski metric transported to the target tangent
model. -/
def transportedInverseMetric (coordinates : Y ≃L[Real] Tangent) :
    (Y →L[Real] Real) →L[Real] (Y →L[Real] Real) →L[Real] Real :=
  ((ContinuousLinearMap.compL Real
      (Y →L[Real] Real) (Tangent →L[Real] Real) Real).flip
      (covectorInStandardCoordinates coordinates)).comp
    (LiuWang2025SemilinearWaveMinkowskiFourNull.inverseMinkowskiMetric.comp
      (covectorInStandardCoordinates coordinates))

@[simp] theorem transportedInverseMetric_apply
    (coordinates : Y ≃L[Real] Tangent)
    (eta zeta : Y →L[Real] Real) :
    transportedInverseMetric coordinates eta zeta =
      LiuWang2025SemilinearWaveMinkowskiFourNull.inverseMinkowskiMetric
        (covectorInStandardCoordinates coordinates eta)
        (covectorInStandardCoordinates coordinates zeta) := rfl

theorem transportedInverseMetric_symmetric
    (coordinates : Y ≃L[Real] Tangent)
    (eta zeta : Y →L[Real] Real) :
    transportedInverseMetric coordinates eta zeta =
      transportedInverseMetric coordinates zeta eta := by
  simp only [transportedInverseMetric_apply]
  exact LiuWang2025SemilinearWaveMinkowskiFourNull.inverseMinkowskiMetric_symmetric _ _

@[simp] theorem transportedInverseMetric_pullback
    (coordinates : Y ≃L[Real] Tangent)
    (xi eta : Tangent →L[Real] Real) :
    transportedInverseMetric coordinates
        (pullbackCovector coordinates xi)
        (pullbackCovector coordinates eta) =
      LiuWang2025SemilinearWaveMinkowskiFourNull.inverseMinkowskiMetric xi eta := by
  simp

/-- The complete Lorentz frame transported from standard Minkowski
coordinates. -/
def transportedFrame (coordinates : Y ≃L[Real] Tangent) :
    LorentzOrthonormalTwoFrame Y where
  inverseMetric := transportedInverseMetric coordinates
  symmetric := transportedInverseMetric_symmetric coordinates
  time := pullbackCovector coordinates
    LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.time
  spatialOne := pullbackCovector coordinates
    LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.spatialOne
  spatialTwo := pullbackCovector coordinates
    LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.spatialTwo
  time_time := by
    simpa using
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.time_time
  time_spatialOne := by
    simpa using
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.time_spatialOne
  time_spatialTwo := by
    simpa using
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.time_spatialTwo
  spatialOne_spatialOne := by
    simpa using
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.spatialOne_spatialOne
  spatialOne_spatialTwo := by
    simpa using
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.spatialOne_spatialTwo
  spatialTwo_spatialTwo := by
    simpa using
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.spatialTwo_spatialTwo

@[simp] theorem transportedFrame_covector
    (coordinates : Y ≃L[Real] Tangent) (j : Fin 4) :
    (transportedFrame coordinates).covector j =
      pullbackCovector coordinates
        (LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.covector j) := by
  fin_cases j <;>
    simp [transportedFrame, LorentzOrthonormalTwoFrame.covector]

@[simp] theorem transportedFrame_weight
    (coordinates : Y ≃L[Real] Tangent) (j : Fin 4) :
    (transportedFrame coordinates).weight j =
      LiuWang2025SemilinearWaveMinkowskiFourNull.standardFrame.weight j := rfl

/-- Affine phases generated directly from the transported phase covectors. -/
def transportedAffinePhase
    (coordinates : Y ≃L[Real] Tangent) (point : Y)
    (j : Fin 4) (y : Y) : Complex :=
  (transportedFrame coordinates).phaseCovector j y -
    (transportedFrame coordinates).phaseCovector j point

@[simp] theorem transportedAffinePhase_at_point
    (coordinates : Y ≃L[Real] Tangent) (point : Y) (j : Fin 4) :
    transportedAffinePhase coordinates point j point = 0 := by
  simp [transportedAffinePhase]

theorem transportedAffinePhase_hasFDerivAt
    (coordinates : Y ≃L[Real] Tangent) (point : Y) (j : Fin 4) :
    HasFDerivAt (transportedAffinePhase coordinates point j)
      ((transportedFrame coordinates).phaseCovector j) point := by
  exact ((transportedFrame coordinates).phaseCovector j).hasFDerivAt.sub_const
    ((transportedFrame coordinates).phaseCovector j point)

/-- The transported affine phase is literally the standard affine phase in
the chosen coordinates. -/
theorem transportedAffinePhase_eq_standard
    (coordinates : Y ≃L[Real] Tangent) (point y : Y) (j : Fin 4) :
    transportedAffinePhase coordinates point j y =
      LiuWang2025SemilinearWaveMinkowskiFourNull.affinePhase
        (coordinates point) j (coordinates y) := by
  simp [transportedAffinePhase,
    LiuWang2025SemilinearWaveMinkowskiFourNull.affinePhase,
    LorentzOrthonormalTwoFrame.phaseCovector,
    transportedFrame_covector]

/-- Coordinate-transported phase-jet packet at an arbitrary target point. -/
def phaseJetData
    (coordinates : Y ≃L[Real] Tangent) (point : Y) :
    LorentzOrthonormalTwoFrame.FourBeamPhaseJetData
      (transportedFrame coordinates) where
  point := point
  phase := transportedAffinePhase coordinates point
  phase_zero := transportedAffinePhase_at_point coordinates point
  phase_hasFDerivAt := transportedAffinePhase_hasFDerivAt coordinates point

/-- Coordinate transport preserves the complete local four-null and critical
phase certificate. -/
def certificate
    (coordinates : Y ≃L[Real] Tangent) (point : Y) :
    LorentzOrthonormalTwoFrame.FourBeamPhaseJetData.Certificate
      (phaseJetData coordinates point) :=
  (phaseJetData coordinates point).certificate

theorem every_covector_future_null_nonzero
    (coordinates : Y ≃L[Real] Tangent) (point : Y) (j : Fin 4) :
    (transportedFrame coordinates).FutureDirected
        ((transportedFrame coordinates).covector j) /\
      (transportedFrame coordinates).Null
        ((transportedFrame coordinates).covector j) /\
      (transportedFrame coordinates).covector j ≠ 0 :=
  (certificate coordinates point).futureNull j

theorem covector_pairwiseDistinct
    (coordinates : Y ≃L[Real] Tangent) (point : Y) :
    Function.Injective (transportedFrame coordinates).covector :=
  (certificate coordinates point).pairwiseDistinct

theorem weighted_covector_sum_eq_zero
    (coordinates : Y ≃L[Real] Tangent) (point : Y) :
    (∑ j,
      (transportedFrame coordinates).weight j •
        (transportedFrame coordinates).covector j) = 0 :=
  (certificate coordinates point).vectorBalance

theorem weightedPhase_at_eq_zero
    (coordinates : Y ≃L[Real] Tangent) (point : Y) :
    weightedPhase (transportedFrame coordinates).weight
        (transportedAffinePhase coordinates point) point = 0 :=
  (certificate coordinates point).phaseBalance.phaseValueZero

theorem weightedPhase_hasFDerivAt_zero
    (coordinates : Y ≃L[Real] Tangent) (point : Y) :
    HasFDerivAt
      (weightedPhase (transportedFrame coordinates).weight
        (transportedAffinePhase coordinates point))
      (0 : Y →L[Real] Complex) point :=
  (phaseJetData coordinates point).toFourBeamPhaseBalanceData
    |>.weightedPhase_hasFDerivAt_zero

end Standard

end LiuWang2025SemilinearWaveTransportedMinkowskiFourNull
