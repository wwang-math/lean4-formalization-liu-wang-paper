import LiuWang.LiuWang2025SemilinearWaveFourNullCovectors
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Liu--Wang 2025: assumption-free Minkowski four-null witness

The general four-null-covector module starts from a Lorentz-orthonormal
time/two-space covector frame.  This file constructs that frame explicitly on
the standard `1 + 2`-dimensional Minkowski model.  Consequently the four
future null covectors, their nonzero weights, their exact balance, and
compatible affine phase first jets are all generated without geometric input.

This is a local normal-form benchmark for the interaction in Section 4.2 of
Liu--Wang.  It does not assert that the standard frame has already been
transported along the paper's broken null geodesics or that those geodesics
meet the accessible boundary with the required transversality.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveMinkowskiFourNull

open LiuWang2025SemilinearWaveFourNullCovectors
open LiuWang2025SemilinearWavePhaseBalance

/-- Standard local tangent model with one time and two spatial coordinates. -/
abbrev Tangent := Fin 3 -> Real

/-- Continuous real covectors on the standard local tangent model. -/
abbrev Covector := Tangent →L[Real] Real

/-- The `i`-th standard basis vector. -/
def basisVector (i : Fin 3) : Tangent :=
  Pi.single i 1

/-- The `i`-th coordinate covector. -/
def coordinateCovector (i : Fin 3) : Covector :=
  ContinuousLinearMap.proj i

/-- Evaluation of a covector on the `i`-th standard basis vector. -/
def covectorCoordinate (i : Fin 3) : Covector →L[Real] Real :=
  ContinuousLinearMap.apply Real Real (basisVector i)

@[simp] theorem coordinateCovector_basisVector
    (i j : Fin 3) :
    coordinateCovector i (basisVector j) = if j = i then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [coordinateCovector, basisVector]
  · simp [coordinateCovector, basisVector, h, Ne.symm h]

/-- Rank-one bilinear form selecting one covector coordinate. -/
def coordinateProduct (i : Fin 3) :
    Covector →L[Real] Covector →L[Real] Real :=
  (covectorCoordinate i).smulRight (covectorCoordinate i)

@[simp] theorem coordinateProduct_apply
    (i : Fin 3) (xi eta : Covector) :
    coordinateProduct i xi eta =
      xi (basisVector i) * eta (basisVector i) := by
  simp [coordinateProduct, covectorCoordinate]

/-- Algebraic inverse Minkowski metric with signature `(-,+,+)` on
covectors. -/
def inverseMinkowskiLinear :
    Covector →ₗ[Real] Covector →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun xi eta =>
      -(xi (basisVector 0) * eta (basisVector 0)) +
        xi (basisVector 1) * eta (basisVector 1) +
        xi (basisVector 2) * eta (basisVector 2))
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

private theorem inverseMinkowskiLinear_bound (xi eta : Covector) :
    ‖inverseMinkowskiLinear xi eta‖ ≤ 3 * ‖xi‖ * ‖eta‖ := by
  have hxi0 : |xi (basisVector 0)| ≤ ‖xi‖ := by
    simpa [basisVector, Pi.norm_single] using
      xi.le_opNorm (basisVector 0)
  have hxi1 : |xi (basisVector 1)| ≤ ‖xi‖ := by
    simpa [basisVector, Pi.norm_single] using
      xi.le_opNorm (basisVector 1)
  have hxi2 : |xi (basisVector 2)| ≤ ‖xi‖ := by
    simpa [basisVector, Pi.norm_single] using
      xi.le_opNorm (basisVector 2)
  have heta0 : |eta (basisVector 0)| ≤ ‖eta‖ := by
    simpa [basisVector, Pi.norm_single] using
      eta.le_opNorm (basisVector 0)
  have heta1 : |eta (basisVector 1)| ≤ ‖eta‖ := by
    simpa [basisVector, Pi.norm_single] using
      eta.le_opNorm (basisVector 1)
  have heta2 : |eta (basisVector 2)| ≤ ‖eta‖ := by
    simpa [basisVector, Pi.norm_single] using
      eta.le_opNorm (basisVector 2)
  have hp0 :
      |xi (basisVector 0)| * |eta (basisVector 0)| ≤ ‖xi‖ * ‖eta‖ :=
    mul_le_mul hxi0 heta0 (abs_nonneg _) (norm_nonneg _)
  have hp1 :
      |xi (basisVector 1)| * |eta (basisVector 1)| ≤ ‖xi‖ * ‖eta‖ :=
    mul_le_mul hxi1 heta1 (abs_nonneg _) (norm_nonneg _)
  have hp2 :
      |xi (basisVector 2)| * |eta (basisVector 2)| ≤ ‖xi‖ * ‖eta‖ :=
    mul_le_mul hxi2 heta2 (abs_nonneg _) (norm_nonneg _)
  change
    |-(xi (basisVector 0) * eta (basisVector 0)) +
        xi (basisVector 1) * eta (basisVector 1) +
        xi (basisVector 2) * eta (basisVector 2)| ≤
      3 * ‖xi‖ * ‖eta‖
  calc
    |-(xi (basisVector 0) * eta (basisVector 0)) +
        xi (basisVector 1) * eta (basisVector 1) +
        xi (basisVector 2) * eta (basisVector 2)| ≤
        |xi (basisVector 0)| * |eta (basisVector 0)| +
          |xi (basisVector 1)| * |eta (basisVector 1)| +
          |xi (basisVector 2)| * |eta (basisVector 2)| := by
      calc
        _ ≤ |-(xi (basisVector 0) * eta (basisVector 0)) +
              xi (basisVector 1) * eta (basisVector 1)| +
              |xi (basisVector 2) * eta (basisVector 2)| := abs_add_le _ _
        _ ≤ (|xi (basisVector 0) * eta (basisVector 0)| +
              |xi (basisVector 1) * eta (basisVector 1)|) +
              |xi (basisVector 2) * eta (basisVector 2)| := by
            gcongr
            simpa using abs_add_le
              (-(xi (basisVector 0) * eta (basisVector 0)))
              (xi (basisVector 1) * eta (basisVector 1))
        _ = _ := by simp [abs_mul]
    _ ≤ 3 * ‖xi‖ * ‖eta‖ := by linarith

/-- The continuous inverse Minkowski metric. -/
def inverseMinkowskiMetric :
    Covector →L[Real] Covector →L[Real] Real :=
  inverseMinkowskiLinear.mkContinuous₂ 3 inverseMinkowskiLinear_bound

theorem inverseMinkowskiMetric_apply (xi eta : Covector) :
    inverseMinkowskiMetric xi eta =
      -(xi (basisVector 0) * eta (basisVector 0)) +
        xi (basisVector 1) * eta (basisVector 1) +
        xi (basisVector 2) * eta (basisVector 2) := rfl

theorem inverseMinkowskiMetric_symmetric (xi eta : Covector) :
    inverseMinkowskiMetric xi eta = inverseMinkowskiMetric eta xi := by
  simp only [inverseMinkowskiMetric_apply]
  ring

/-- Completely explicit Lorentz-orthonormal covector frame in the standard
Minkowski normal form. -/
def standardFrame : LorentzOrthonormalTwoFrame Tangent where
  inverseMetric := inverseMinkowskiMetric
  symmetric := inverseMinkowskiMetric_symmetric
  time := coordinateCovector 0
  spatialOne := coordinateCovector 1
  spatialTwo := coordinateCovector 2
  time_time := by
    simp [inverseMinkowskiMetric_apply, Fin.ext_iff]
  time_spatialOne := by
    simp [inverseMinkowskiMetric_apply, Fin.ext_iff]
  time_spatialTwo := by
    simp [inverseMinkowskiMetric_apply, Fin.ext_iff]
  spatialOne_spatialOne := by
    simp [inverseMinkowskiMetric_apply, Fin.ext_iff]
  spatialOne_spatialTwo := by
    simp [inverseMinkowskiMetric_apply, Fin.ext_iff]
  spatialTwo_spatialTwo := by
    simp [inverseMinkowskiMetric_apply, Fin.ext_iff]

/-- Affine phase with the prescribed standard null covector and value zero at
the selected interaction point. -/
def affinePhase (point : Tangent) (j : Fin 4) (x : Tangent) : Complex :=
  standardFrame.phaseCovector j x - standardFrame.phaseCovector j point

@[simp] theorem affinePhase_at_point (point : Tangent) (j : Fin 4) :
    affinePhase point j point = 0 := by
  simp [affinePhase]

theorem affinePhase_hasFDerivAt (point : Tangent) (j : Fin 4) :
    HasFDerivAt (affinePhase point j) (standardFrame.phaseCovector j) point := by
  have h : HasFDerivAt
      (fun x : Tangent => standardFrame.phaseCovector j x)
      (standardFrame.phaseCovector j) point :=
    (standardFrame.phaseCovector j).hasFDerivAt
  exact h.sub_const (standardFrame.phaseCovector j point)

/-- Assumption-free phase-jet packet at an arbitrary local interaction point. -/
def phaseJetData (point : Tangent) :
    LorentzOrthonormalTwoFrame.FourBeamPhaseJetData standardFrame where
  point := point
  phase := affinePhase point
  phase_zero := affinePhase_at_point point
  phase_hasFDerivAt := affinePhase_hasFDerivAt point

/-- The four standard covectors are future directed, null, nonzero, pairwise
distinct, and exactly balanced; their affine phases generate the critical
combined phase and every replicated higher-order phase. -/
def certificate (point : Tangent) :
    LorentzOrthonormalTwoFrame.FourBeamPhaseJetData.Certificate
      (phaseJetData point) :=
  (phaseJetData point).certificate

theorem weighted_covector_sum_eq_zero :
    (∑ j, standardFrame.weight j • standardFrame.covector j) = 0 :=
  standardFrame.weighted_covector_sum_eq_zero

theorem weightedPhase_at_eq_zero (point : Tangent) :
    weightedPhase standardFrame.weight (affinePhase point) point = 0 :=
  (phaseJetData point).toFourBeamPhaseBalanceData.weightedPhase_at_eq_zero

theorem weightedPhase_hasFDerivAt_zero (point : Tangent) :
    HasFDerivAt
      (weightedPhase standardFrame.weight (affinePhase point))
      (0 : Tangent →L[Real] Complex) point :=
  (phaseJetData point).toFourBeamPhaseBalanceData
    |>.weightedPhase_hasFDerivAt_zero

theorem every_covector_future_null_nonzero (j : Fin 4) :
    standardFrame.FutureDirected (standardFrame.covector j) /\
      standardFrame.Null (standardFrame.covector j) /\
      standardFrame.covector j ≠ 0 :=
  (certificate 0).futureNull j

end LiuWang2025SemilinearWaveMinkowskiFourNull
