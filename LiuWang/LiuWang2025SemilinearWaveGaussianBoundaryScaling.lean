import LiuWang.LiuWang2025SemilinearWaveReflectedPhaseMismatch
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Liu--Wang 2025: dimension-audited Gaussian boundary scaling

The last step in the proof of equations (3.14) and (3.17) integrates the
pointwise reflected-beam derivative estimate

`rho^r |y|^(r + N + 1 - j) exp (-c rho |y|^2)`,  `r + j = |alpha|`,

over the transverse boundary variables.  This module verifies the radial
Gaussian moment by Mathlib's Gamma-integral theorem and checks the complete
frequency-exponent calculation.  Every summand has squared-mass exponent

`-(N - |alpha| + 1) - d/2`,

so its `L^2` exponent is

`-(N - |alpha| + 1)/2 - d/4`

when there are `d` transverse integration variables.

The displayed exponent `3/4` in arXiv:2511.08794v1 is therefore the
specialization `d = 3`.  For a dimension-uniform theorem the Gaussian
calculation gives `d/4`.  This module records that distinction explicitly;
it does not yet construct the boundary chart, control its volume density, or
derive the multi-index pointwise estimate from the geometric phase and
amplitude jets.
-/

noncomputable section

open Filter MeasureTheory Set Topology

namespace LiuWang2025SemilinearWaveGaussianBoundaryScaling

open LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay
open LiuWang2025SemilinearWaveGaussianRecovery

/-- Radial part of the squared Gaussian moment after polar coordinates.  The
surface-area constant is intentionally omitted because it is independent of
the frequency parameter. -/
def radialSquaredGaussianMoment
    (momentPower damping rho : Real) : Real :=
  ∫ r in Ioi (0 : Real),
    r ^ momentPower * Real.exp (-(2 * damping * rho) * r ^ (2 : Real))

/-- Exact Gamma-function evaluation of the radial squared Gaussian moment. -/
theorem radialSquaredGaussianMoment_formula
    {momentPower damping rho : Real}
    (hmoment : -1 < momentPower) (hdamping : 0 < damping)
    (hrho : 0 < rho) :
    radialSquaredGaussianMoment momentPower damping rho =
      (2 * damping * rho) ^ (-(momentPower + 1) / 2) *
        (1 / 2 : Real) * Real.Gamma ((momentPower + 1) / 2) := by
  unfold radialSquaredGaussianMoment
  exact integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : Real)) (q := momentPower) (b := 2 * damping * rho)
    (by norm_num) hmoment (by positivity)

/-- Radial power produced by squaring one source derivative term and adding
the `d - 1` polar-coordinate Jacobian power. -/
def sourceRadialPower
    (d N phaseHits amplitudeLoss : Nat) : Real :=
  2 * ((phaseHits : Real) + (N : Real) + 1 - (amplitudeLoss : Real)) +
    (d : Real) - 1

theorem sourceRadialPower_gt_neg_one
    {d N phaseHits amplitudeLoss : Nat}
    (hd : 1 <= d) (hloss : amplitudeLoss <= phaseHits + N + 1) :
    -1 < sourceRadialPower d N phaseHits amplitudeLoss := by
  have hdReal : (1 : Real) <= (d : Real) := by exact_mod_cast hd
  have hlossReal :
      (amplitudeLoss : Real) <=
        (phaseHits : Real) + (N : Real) + 1 := by
    exact_mod_cast hloss
  unfold sourceRadialPower
  linarith

/-- Exact radial moment for one term in the derivative expansion appearing
between equations (3.16) and (3.17). -/
theorem sourceRadialSquaredGaussianMoment_formula
    {d N phaseHits amplitudeLoss : Nat} {damping rho : Real}
    (hd : 1 <= d) (hloss : amplitudeLoss <= phaseHits + N + 1)
    (hdamping : 0 < damping) (hrho : 0 < rho) :
    radialSquaredGaussianMoment
        (sourceRadialPower d N phaseHits amplitudeLoss) damping rho =
      (2 * damping * rho) ^
          (-(sourceRadialPower d N phaseHits amplitudeLoss + 1) / 2) *
        (1 / 2 : Real) *
          Real.Gamma
            ((sourceRadialPower d N phaseHits amplitudeLoss + 1) / 2) :=
  radialSquaredGaussianMoment_formula
    (sourceRadialPower_gt_neg_one hd hloss) hdamping hrho

/-- Frequency exponent after multiplying the squared radial moment by the
prefactor `rho^(2 phaseHits)`. -/
def sourceSquaredMassExponent
    (d N phaseHits amplitudeLoss : Nat) : Real :=
  2 * (phaseHits : Real) -
    (sourceRadialPower d N phaseHits amplitudeLoss + 1) / 2

/-- The raw exponent calculation before using `phaseHits + amplitudeLoss =
|alpha|`. -/
theorem sourceSquaredMassExponent_eq
    (d N phaseHits amplitudeLoss : Nat) :
    sourceSquaredMassExponent d N phaseHits amplitudeLoss =
      (phaseHits : Real) - (N : Real) - 1 +
        (amplitudeLoss : Real) - (d : Real) / 2 := by
  unfold sourceSquaredMassExponent sourceRadialPower
  ring

/-- All derivative-distribution summands have the same squared-mass exponent.
This is the key cancellation hidden by the paper's phrase "by induction". -/
theorem sourceSquaredMassExponent_collapse
    {d N phaseHits amplitudeLoss derivativeOrder : Nat}
    (horder : phaseHits + amplitudeLoss = derivativeOrder) :
    sourceSquaredMassExponent d N phaseHits amplitudeLoss =
      -((N : Real) - (derivativeOrder : Real) + 1) - (d : Real) / 2 := by
  rw [sourceSquaredMassExponent_eq]
  have horderReal :
      (phaseHits : Real) + (amplitudeLoss : Real) =
        (derivativeOrder : Real) := by
    exact_mod_cast horder
  linarith

/-- Dimension-correct positive decay exponent for the boundary `L^2` or
Sobolev norm. -/
def dimensionCorrectBoundaryDecayExponent
    (d N derivativeOrder : Nat) : Real :=
  ((N : Real) - (derivativeOrder : Real) + 1) / 2 + (d : Real) / 4

/-- The squared-mass exponent is minus twice the norm-decay exponent. -/
theorem sourceSquaredMassExponent_eq_neg_two_decayExponent
    {d N phaseHits amplitudeLoss derivativeOrder : Nat}
    (horder : phaseHits + amplitudeLoss = derivativeOrder) :
    sourceSquaredMassExponent d N phaseHits amplitudeLoss =
      -2 * dimensionCorrectBoundaryDecayExponent d N derivativeOrder := by
  rw [sourceSquaredMassExponent_collapse horder]
  unfold dimensionCorrectBoundaryDecayExponent
  ring

theorem dimensionCorrectBoundaryDecayExponent_pos
    {d N derivativeOrder : Nat}
    (hd : 1 <= d) (hderivative : derivativeOrder <= N + 1) :
    0 < dimensionCorrectBoundaryDecayExponent d N derivativeOrder := by
  have hdReal : (1 : Real) <= (d : Real) := by exact_mod_cast hd
  have hderivativeReal :
      (derivativeOrder : Real) <= (N : Real) + 1 := by
    exact_mod_cast hderivative
  unfold dimensionCorrectBoundaryDecayExponent
  linarith

/-- Dimension-correct frequency-indexed boundary rate. -/
def dimensionCorrectBoundaryDecayRate
    (d N derivativeOrder rho : Nat) : Real :=
  (rho : Real) ^
    (-dimensionCorrectBoundaryDecayExponent d N derivativeOrder)

theorem dimensionCorrectBoundaryDecayRate_tendsto_zero
    {d N derivativeOrder : Nat}
    (hd : 1 <= d) (hderivative : derivativeOrder <= N + 1) :
    Tendsto (dimensionCorrectBoundaryDecayRate d N derivativeOrder)
      atTop (nhds 0) := by
  exact
    (tendsto_rpow_neg_atTop
      (dimensionCorrectBoundaryDecayExponent_pos hd hderivative)).comp
        tendsto_natCast_atTop_atTop

/-- A boundary packet carrying the dimension-correct version of the estimate
derived by the Gaussian change of variables. -/
structure DimensionCorrectBoundaryDecayPacket
    (E : Type*) [SeminormedAddCommGroup E] where
  transverseDimension : Nat
  order : Nat
  derivativeOrder : Nat
  boundaryTrace : Nat -> E
  boundConstant : Real
  transverseDimension_pos : 1 <= transverseDimension
  derivativeOrder_le : derivativeOrder <= order + 1
  boundConstant_nonneg : 0 <= boundConstant
  norm_boundaryTrace_le : forall rho,
    ‖boundaryTrace rho‖ <=
      boundConstant * dimensionCorrectBoundaryDecayRate
        transverseDimension order derivativeOrder rho

namespace DimensionCorrectBoundaryDecayPacket

variable {E : Type*} [SeminormedAddCommGroup E]

theorem exponent_pos (packet : DimensionCorrectBoundaryDecayPacket E) :
    0 < dimensionCorrectBoundaryDecayExponent packet.transverseDimension
      packet.order packet.derivativeOrder :=
  dimensionCorrectBoundaryDecayExponent_pos
    packet.transverseDimension_pos packet.derivativeOrder_le

/-- The corrected dimension-dependent estimate is already sufficient for the
inaccessible-boundary limit used in equations (4.5)--(4.6). -/
theorem boundaryTrace_tendsto_zero
    (packet : DimensionCorrectBoundaryDecayPacket E) :
    Tendsto packet.boundaryTrace atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun rho => norm_nonneg (packet.boundaryTrace rho))
    packet.norm_boundaryTrace_le
  simpa using
    tendsto_const_nhds.mul
      (dimensionCorrectBoundaryDecayRate_tendsto_zero
        packet.transverseDimension_pos packet.derivativeOrder_le)

end DimensionCorrectBoundaryDecayPacket

/-- Point-recovery data using the dimension-correct reflected-boundary rate.
This is a repaired route for the final limiting argument rather than merely a
diagnostic about the displayed exponent. -/
structure DimensionCorrectRatePointRecoveryData where
  coefficient : Complex
  stationaryConstant : Complex
  amplitudeProduct : Complex
  principal : Nat -> Complex
  error : Nat -> Complex
  boundary : Nat -> Complex
  transverseDimension : Nat
  order : Nat
  derivativeOrder : Nat
  boundaryConstant : Real
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  amplitudeProduct_ne_zero : amplitudeProduct ≠ 0
  transverseDimension_pos : 1 <= transverseDimension
  derivativeOrder_le : derivativeOrder <= order + 1
  boundaryConstant_nonneg : 0 <= boundaryConstant
  principal_tendsto : Tendsto principal atTop
    (nhds (stationaryConstant * coefficient * amplitudeProduct))
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  boundary_rate : forall rho,
    ‖boundary rho‖ <=
      boundaryConstant * dimensionCorrectBoundaryDecayRate
        transverseDimension order derivativeOrder rho
  integralIdentity : forall rho, principal rho + error rho = boundary rho

namespace DimensionCorrectRatePointRecoveryData

/-- Forgetful map to the checked abstract recovery theorem, with the boundary
limit generated from the corrected rate. -/
def toPointRecoveryData
    (data : DimensionCorrectRatePointRecoveryData) : PointRecoveryData where
  coefficient := data.coefficient
  stationaryConstant := data.stationaryConstant
  amplitudeProduct := data.amplitudeProduct
  principal := data.principal
  error := data.error
  boundary := data.boundary
  stationaryConstant_ne_zero := data.stationaryConstant_ne_zero
  amplitudeProduct_ne_zero := data.amplitudeProduct_ne_zero
  principal_tendsto := data.principal_tendsto
  error_tendsto_zero := data.error_tendsto_zero
  inaccessibleBoundary_tendsto_zero := by
    let packet : DimensionCorrectBoundaryDecayPacket Complex := {
      transverseDimension := data.transverseDimension
      order := data.order
      derivativeOrder := data.derivativeOrder
      boundaryTrace := data.boundary
      boundConstant := data.boundaryConstant
      transverseDimension_pos := data.transverseDimension_pos
      derivativeOrder_le := data.derivativeOrder_le
      boundConstant_nonneg := data.boundaryConstant_nonneg
      norm_boundaryTrace_le := data.boundary_rate
    }
    exact packet.boundaryTrace_tendsto_zero
  integralIdentity := data.integralIdentity

/-- The dimension correction does not weaken the paper's coefficient-recovery
endpoint: the corrected decay exponent remains strictly positive. -/
theorem coefficient_eq_zero
    (data : DimensionCorrectRatePointRecoveryData) :
    data.coefficient = 0 :=
  data.toPointRecoveryData.coefficient_eq_zero

structure Certificate (data : DimensionCorrectRatePointRecoveryData) : Prop where
  dimensionCorrectExponentPositive :
    0 < dimensionCorrectBoundaryDecayExponent data.transverseDimension
      data.order data.derivativeOrder
  inaccessibleBoundaryVanishes : Tendsto data.boundary atTop (nhds 0)
  coefficientZero : data.coefficient = 0

def certificate (data : DimensionCorrectRatePointRecoveryData) :
    Certificate data where
  dimensionCorrectExponentPositive :=
    dimensionCorrectBoundaryDecayExponent_pos
      data.transverseDimension_pos data.derivativeOrder_le
  inaccessibleBoundaryVanishes := data.toPointRecoveryData.inaccessibleBoundary_tendsto_zero
  coefficientZero := data.coefficient_eq_zero

end DimensionCorrectRatePointRecoveryData

/-- The paper's displayed `3/4` exponent is exactly the three-dimensional
specialization of the dimension-correct Gaussian calculation. -/
theorem dimensionCorrectBoundaryDecayExponent_three
    (N derivativeOrder : Nat) :
    dimensionCorrectBoundaryDecayExponent 3 N derivativeOrder =
      boundaryDecayExponent N derivativeOrder := by
  unfold dimensionCorrectBoundaryDecayExponent boundaryDecayExponent
  norm_num

/-- Conversely, the dimension-correct exponent agrees with the displayed
paper exponent precisely in transverse dimension three. -/
theorem dimensionCorrectBoundaryDecayExponent_eq_paper_iff
    (d N derivativeOrder : Nat) :
    dimensionCorrectBoundaryDecayExponent d N derivativeOrder =
        boundaryDecayExponent N derivativeOrder <->
      d = 3 := by
  constructor
  · intro h
    have hdReal : (d : Real) = 3 := by
      unfold dimensionCorrectBoundaryDecayExponent boundaryDecayExponent at h
      linarith
    exact_mod_cast hdReal
  · intro hd
    subst d
    exact dimensionCorrectBoundaryDecayExponent_three N derivativeOrder

/-- For at least three transverse variables, the dimension-correct exponent
is no smaller than the paper's conservative `3/4` exponent.  The only
dimension named in the main theorem that needs a textual correction is
therefore `d = 2`. -/
theorem paperBoundaryDecayExponent_le_dimensionCorrect
    {d N derivativeOrder : Nat} (hd : 3 <= d) :
    boundaryDecayExponent N derivativeOrder <=
      dimensionCorrectBoundaryDecayExponent d N derivativeOrder := by
  have hdReal : (3 : Real) <= (d : Real) := by exact_mod_cast hd
  unfold boundaryDecayExponent dimensionCorrectBoundaryDecayExponent
  linarith

/-- Product-facing certificate for the audited change-of-variables step. -/
structure Certificate : Prop where
  radialMoment :
    forall {momentPower damping rho : Real},
      -1 < momentPower -> 0 < damping -> 0 < rho ->
      radialSquaredGaussianMoment momentPower damping rho =
        (2 * damping * rho) ^ (-(momentPower + 1) / 2) *
          (1 / 2 : Real) * Real.Gamma ((momentPower + 1) / 2)
  exponentCollapse :
    forall {d N phaseHits amplitudeLoss derivativeOrder : Nat},
      phaseHits + amplitudeLoss = derivativeOrder ->
      sourceSquaredMassExponent d N phaseHits amplitudeLoss =
        -2 * dimensionCorrectBoundaryDecayExponent d N derivativeOrder
  paperExponentAudit :
    forall d N derivativeOrder,
      dimensionCorrectBoundaryDecayExponent d N derivativeOrder =
          boundaryDecayExponent N derivativeOrder <->
        d = 3
  correctedRateVanishes :
    forall {d N derivativeOrder : Nat},
      1 <= d -> derivativeOrder <= N + 1 ->
      Tendsto (dimensionCorrectBoundaryDecayRate d N derivativeOrder)
        atTop (nhds 0)
  correctedRateClosesRecovery :
    forall data : DimensionCorrectRatePointRecoveryData,
      data.coefficient = 0

def certificate : Certificate where
  radialMoment := fun hmoment hdamping hrho =>
    radialSquaredGaussianMoment_formula hmoment hdamping hrho
  exponentCollapse := fun horder =>
    sourceSquaredMassExponent_eq_neg_two_decayExponent horder
  paperExponentAudit := dimensionCorrectBoundaryDecayExponent_eq_paper_iff
  correctedRateVanishes := fun hd hderivative =>
    dimensionCorrectBoundaryDecayRate_tendsto_zero hd hderivative
  correctedRateClosesRecovery := fun data => data.coefficient_eq_zero

end LiuWang2025SemilinearWaveGaussianBoundaryScaling
