import LiuWang.LiuWang2025SemilinearWaveBeamProductRemainder

/-!
# Liu--Wang 2025: equation-(3.11)-to-(3.12) energy/Sobolev closure

The Gaussian-beam quasimode in Liu--Wang satisfies the source residual estimate

`||Box_g v_rho||_{H^k} = O(rho^-K)`,

where

`K = (N + 1) / 2 + n / 4 - k - 2`.

The exact correction solves the zero-data wave equation with forcing
`-Box_g v_rho`.  A hyperbolic energy estimate followed by Sobolev embedding
therefore transfers the residual rate to a uniform pointwise rate.  This
module verifies the complete quantitative transfer, including an explicit
beam order `N = n + 2k + 8` that is sufficient for the equation-(3.12) target

`||r_rho||_C = O(rho^-((n+1)/2+2))`.

The concrete globally hyperbolic wave solution operator, the concrete
Sobolev embedding, and the WKB proof of the equation-(3.11) residual estimate
remain source-facing analytic inputs.  The exponent choice and the passage
through those bounded operators to equation (3.12) are theorems.
-/

noncomputable section

open Filter Topology

namespace LiuWang2025SemilinearWaveEquation312EnergyClosure

open LiuWang2025SemilinearWaveBeamProductRemainder
open LiuWang2025SemilinearWaveEquation44QuantitativeRecovery

/-- The decay exponent `K` in equation (3.11), with `n` the spatial
dimension, `N` the Gaussian-beam expansion order, and `k` the residual
Sobolev order. -/
def equation311DecayExponent
    (spatialDimension beamOrder residualDerivativeOrder : Nat) : Real :=
  ((beamOrder + 1 : Nat) : Real) / 2 +
    (spatialDimension : Real) / 4 -
    (residualDerivativeOrder : Real) - 2

/-- The target positive decay exponent in equation (3.12). -/
def equation312TargetExponent (spatialDimension : Nat) : Real :=
  ((spatialDimension + 1 : Nat) : Real) / 2 + 2

/-- The integer order condition exactly equivalent to the elementary
inequality needed to dominate the equation-(3.11) rate by equation (3.12). -/
def Equation312OrderCondition
    (spatialDimension beamOrder residualDerivativeOrder : Nat) : Prop :=
  spatialDimension + 4 * residualDerivativeOrder + 16 <= 2 * beamOrder

/-- A simple explicit beam order replacing the source phrase "choose `N`
sufficiently large."  It is not claimed to be the minimal integer choice. -/
def certifiedBeamOrder
    (spatialDimension residualDerivativeOrder : Nat) : Nat :=
  spatialDimension + 2 * residualDerivativeOrder + 8

theorem certifiedBeamOrder_satisfies
    (spatialDimension residualDerivativeOrder : Nat) :
    Equation312OrderCondition spatialDimension
      (certifiedBeamOrder spatialDimension residualDerivativeOrder)
      residualDerivativeOrder := by
  unfold Equation312OrderCondition certifiedBeamOrder
  omega

/-- The explicit integer order condition implies that the source residual
decays at least as fast as the equation-(3.12) target. -/
theorem equation312TargetExponent_le_equation311DecayExponent
    {spatialDimension beamOrder residualDerivativeOrder : Nat}
    (horder : Equation312OrderCondition spatialDimension beamOrder
      residualDerivativeOrder) :
    equation312TargetExponent spatialDimension <=
      equation311DecayExponent spatialDimension beamOrder
        residualDerivativeOrder := by
  have horderReal :
      (spatialDimension : Real) +
          4 * (residualDerivativeOrder : Real) + 16 <=
        2 * (beamOrder : Real) := by
    exact_mod_cast horder
  unfold equation312TargetExponent equation311DecayExponent
  push_cast
  linarith

/-- Integer-frequency version of the equation-(3.11) residual rate. -/
def equation311ResidualRate
    (spatialDimension beamOrder residualDerivativeOrder rho : Nat) : Real :=
  (rho : Real) ^
    (-equation311DecayExponent spatialDimension beamOrder
      residualDerivativeOrder)

theorem equation311ResidualRate_nonneg
    (spatialDimension beamOrder residualDerivativeOrder rho : Nat) :
    0 <= equation311ResidualRate spatialDimension beamOrder
      residualDerivativeOrder rho := by
  exact Real.rpow_nonneg (Nat.cast_nonneg rho) _

/-- The source residual rate is bounded by the equation-(3.12) pointwise
remainder rate once the explicit order condition holds. -/
theorem equation311ResidualRate_le_sourceBeamRemainderRate
    {spatialDimension beamOrder residualDerivativeOrder rho : Nat}
    (horder : Equation312OrderCondition spatialDimension beamOrder
      residualDerivativeOrder)
    (hrho : 1 <= rho) :
    equation311ResidualRate spatialDimension beamOrder
        residualDerivativeOrder rho <=
      sourceBeamRemainderRate (spatialDimension + 1) rho := by
  have hbase : (1 : Real) <= (rho : Real) := by
    exact_mod_cast hrho
  have hexponent :=
    equation312TargetExponent_le_equation311DecayExponent horder
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase (neg_le_neg hexponent)
  simpa [equation311ResidualRate, sourceBeamRemainderRate,
    equation312TargetExponent] using hpow

variable {Omega ForcingSpace EnergySpace ContinuousSpace : Type*}
  [NormedAddCommGroup ForcingSpace] [NormedSpace Complex ForcingSpace]
  [NormedAddCommGroup EnergySpace] [NormedSpace Complex EnergySpace]
  [NormedAddCommGroup ContinuousSpace] [NormedSpace Complex ContinuousSpace]

/-- Source-facing operator realization of the argument following equation
(3.11): solve the zero-data wave equation, embed the energy/Sobolev solution
into a continuous carrier, and evaluate it pointwise. -/
structure Equation312RemainderData
    (spatialDimension beamOrder residualDerivativeOrder : Nat) where
  orderCondition : Equation312OrderCondition spatialDimension beamOrder
    residualDerivativeOrder
  forcing : Nat -> ForcingSpace
  waveSolution : ForcingSpace →L[Complex] EnergySpace
  sobolevEmbedding : EnergySpace →L[Complex] ContinuousSpace
  pointEvaluation : Omega -> ContinuousSpace →L[Complex] Complex
  pointEvaluation_norm_le_one : forall x, ‖pointEvaluation x‖ <= 1
  residualConstant : Real
  residualConstant_nonneg : 0 <= residualConstant
  equation311ResidualEstimate : ∀ᶠ rho in atTop,
    ‖forcing rho‖ <=
      residualConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho

namespace Equation312RemainderData

variable {spatialDimension beamOrder residualDerivativeOrder : Nat}

/-- The exact wave correction in the energy/Sobolev carrier. -/
def energyRemainder
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder)
    (rho : Nat) : EnergySpace :=
  data.waveSolution (data.forcing rho)

/-- The correction after the source Sobolev embedding. -/
def continuousRemainder
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder)
    (rho : Nat) : ContinuousSpace :=
  data.sobolevEmbedding (data.energyRemainder rho)

/-- Pointwise correction consumed by the four-beam product estimate. -/
def pointwiseRemainder
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder)
    (rho : Nat) (x : Omega) : Complex :=
  data.pointEvaluation x (data.continuousRemainder rho)

/-- Explicit constant obtained from the residual estimate, wave energy
operator, and Sobolev embedding. -/
def equation312RemainderConstant
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder) : Real :=
  ‖data.sobolevEmbedding‖ * ‖data.waveSolution‖ * data.residualConstant

theorem equation312RemainderConstant_nonneg
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder) :
    0 <= data.equation312RemainderConstant := by
  exact mul_nonneg
    (mul_nonneg (norm_nonneg data.sobolevEmbedding)
      (norm_nonneg data.waveSolution))
    data.residualConstant_nonneg

/-- The checked form of equation (3.12): the source residual estimate,
bounded wave solution map, and Sobolev embedding generate a uniform
pointwise remainder estimate with the exact paper exponent. -/
theorem pointwiseRemainder_rate
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder) :
    ∀ᶠ rho in atTop, forall x,
      ‖data.pointwiseRemainder rho x‖ <=
        data.equation312RemainderConstant *
          sourceBeamRemainderRate (spatialDimension + 1) rho := by
  have hrhoLarge : ∀ᶠ rho : Nat in atTop, 1 <= rho :=
    eventually_ge_atTop 1
  filter_upwards [data.equation311ResidualEstimate, hrhoLarge]
    with rho hresidual hrho
  intro x
  have hevaluation :
      ‖data.pointwiseRemainder rho x‖ <=
        ‖data.continuousRemainder rho‖ := by
    calc
      ‖data.pointwiseRemainder rho x‖ <=
          ‖data.pointEvaluation x‖ *
            ‖data.continuousRemainder rho‖ :=
        (data.pointEvaluation x).le_opNorm _
      _ <= 1 * ‖data.continuousRemainder rho‖ := by
        gcongr
        exact data.pointEvaluation_norm_le_one x
      _ = ‖data.continuousRemainder rho‖ := one_mul _
  have hembedding :
      ‖data.continuousRemainder rho‖ <=
        ‖data.sobolevEmbedding‖ * ‖data.energyRemainder rho‖ :=
    data.sobolevEmbedding.le_opNorm _
  have hwave :
      ‖data.energyRemainder rho‖ <=
        ‖data.waveSolution‖ * ‖data.forcing rho‖ :=
    data.waveSolution.le_opNorm _
  have hrate := equation311ResidualRate_le_sourceBeamRemainderRate
    data.orderCondition hrho
  calc
    ‖data.pointwiseRemainder rho x‖ <=
        ‖data.continuousRemainder rho‖ := hevaluation
    _ <= ‖data.sobolevEmbedding‖ * ‖data.energyRemainder rho‖ :=
      hembedding
    _ <= ‖data.sobolevEmbedding‖ *
        (‖data.waveSolution‖ * ‖data.forcing rho‖) := by
      exact mul_le_mul_of_nonneg_left hwave
        (norm_nonneg data.sobolevEmbedding)
    _ <= ‖data.sobolevEmbedding‖ *
        (‖data.waveSolution‖ *
          (data.residualConstant *
            equation311ResidualRate spatialDimension beamOrder
              residualDerivativeOrder rho)) := by
      gcongr
    _ = data.equation312RemainderConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho := by
      unfold equation312RemainderConstant
      ring
    _ <= data.equation312RemainderConstant *
        sourceBeamRemainderRate (spatialDimension + 1) rho :=
      mul_le_mul_of_nonneg_left hrate
        data.equation312RemainderConstant_nonneg

/-- Product certificate for the equation-(3.11)-to-(3.12) transfer. -/
structure Certificate
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder) : Prop where
  orderIsSufficient : Equation312OrderCondition spatialDimension beamOrder
    residualDerivativeOrder
  targetExponentDominated :
    equation312TargetExponent spatialDimension <=
      equation311DecayExponent spatialDimension beamOrder
        residualDerivativeOrder
  remainderConstantNonnegative : 0 <= data.equation312RemainderConstant
  equation312PointwiseRate : ∀ᶠ rho in atTop, forall x,
    ‖data.pointwiseRemainder rho x‖ <=
      data.equation312RemainderConstant *
        sourceBeamRemainderRate (spatialDimension + 1) rho

def certificate
    (data : Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder) :
    Certificate data where
  orderIsSufficient := data.orderCondition
  targetExponentDominated :=
    equation312TargetExponent_le_equation311DecayExponent
      data.orderCondition
  remainderConstantNonnegative := data.equation312RemainderConstant_nonneg
  equation312PointwiseRate := data.pointwiseRemainder_rate

end Equation312RemainderData

open MeasureTheory

variable [MeasurableSpace Omega]

/-- Four equation-(3.12) correction families together with the coefficient
and principal beams used in the cubic interaction.  This adapter is the
source-facing bridge from the energy/Sobolev closure above to the existing
four-beam equation-(4.4) product theorem. -/
structure FourBeamEquation312Data
    (mu : Measure Omega)
    (spatialDimension beamOrder residualDerivativeOrder : Nat) where
  beam0 : Equation312RemainderData
    (Omega := Omega) (ForcingSpace := ForcingSpace)
    (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
    spatialDimension beamOrder residualDerivativeOrder
  beam1 : Equation312RemainderData
    (Omega := Omega) (ForcingSpace := ForcingSpace)
    (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
    spatialDimension beamOrder residualDerivativeOrder
  beam2 : Equation312RemainderData
    (Omega := Omega) (ForcingSpace := ForcingSpace)
    (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
    spatialDimension beamOrder residualDerivativeOrder
  beam3 : Equation312RemainderData
    (Omega := Omega) (ForcingSpace := ForcingSpace)
    (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
    spatialDimension beamOrder residualDerivativeOrder
  coefficient : Omega -> Complex
  principal0 : Nat -> Omega -> Complex
  principal1 : Nat -> Omega -> Complex
  principal2 : Nat -> Omega -> Complex
  principal3 : Nat -> Omega -> Complex
  coefficientBound : Real
  principalBound : Real
  coefficientBound_nonneg : 0 <= coefficientBound
  principalBound_nonneg : 0 <= principalBound
  largePrincipalBounds : ∀ᶠ rho in atTop, forall x,
    ‖coefficient x‖ <= coefficientBound ∧
    ‖principal0 rho x‖ <= principalBound ∧
    ‖principal1 rho x‖ <= principalBound ∧
    ‖principal2 rho x‖ <= principalBound ∧
    ‖principal3 rho x‖ <= principalBound
  integrableProductError : forall rho, Integrable (fun x =>
    coefficient x *
      ((principal0 rho x + beam0.pointwiseRemainder rho x) *
          (principal1 rho x + beam1.pointwiseRemainder rho x) *
          (principal2 rho x + beam2.pointwiseRemainder rho x) *
          (principal3 rho x + beam3.pointwiseRemainder rho x) -
        principal0 rho x * principal1 rho x *
          principal2 rho x * principal3 rho x)) mu

namespace FourBeamEquation312Data

variable {mu : Measure Omega} [IsFiniteMeasure mu]
variable {spatialDimension beamOrder residualDerivativeOrder : Nat}

/-- A common remainder constant for the four source corrections. -/
def uniformRemainderConstant
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) : Real :=
  max
    (max data.beam0.equation312RemainderConstant
      data.beam1.equation312RemainderConstant)
    (max data.beam2.equation312RemainderConstant
      data.beam3.equation312RemainderConstant)

omit [IsFiniteMeasure mu] in
theorem beam0_constant_le_uniform
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    data.beam0.equation312RemainderConstant <=
      data.uniformRemainderConstant := by
  unfold uniformRemainderConstant
  exact (le_max_left _ _).trans (le_max_left _ _)

omit [IsFiniteMeasure mu] in
theorem beam1_constant_le_uniform
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    data.beam1.equation312RemainderConstant <=
      data.uniformRemainderConstant := by
  unfold uniformRemainderConstant
  exact (le_max_right _ _).trans (le_max_left _ _)

omit [IsFiniteMeasure mu] in
theorem beam2_constant_le_uniform
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    data.beam2.equation312RemainderConstant <=
      data.uniformRemainderConstant := by
  unfold uniformRemainderConstant
  exact (le_max_left _ _).trans (le_max_right _ _)

omit [IsFiniteMeasure mu] in
theorem beam3_constant_le_uniform
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    data.beam3.equation312RemainderConstant <=
      data.uniformRemainderConstant := by
  unfold uniformRemainderConstant
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem uniformRemainderConstant_nonneg
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    0 <= data.uniformRemainderConstant := by
  exact le_trans data.beam0.equation312RemainderConstant_nonneg
    data.beam0_constant_le_uniform

/-- The four equation-(3.12) energy/Sobolev packets instantiate the exact
remainder fields and uniform pointwise estimate required by the checked
four-beam product theorem. -/
def toBeamProductRemainderData
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    BeamProductRemainderData mu where
  spaceTimeDimension := spatialDimension + 1
  coefficient := data.coefficient
  principal0 := data.principal0
  principal1 := data.principal1
  principal2 := data.principal2
  principal3 := data.principal3
  remainder0 := data.beam0.pointwiseRemainder
  remainder1 := data.beam1.pointwiseRemainder
  remainder2 := data.beam2.pointwiseRemainder
  remainder3 := data.beam3.pointwiseRemainder
  coefficientBound := data.coefficientBound
  principalBound := data.principalBound
  remainderConstant := data.uniformRemainderConstant
  coefficientBound_nonneg := data.coefficientBound_nonneg
  principalBound_nonneg := data.principalBound_nonneg
  remainderConstant_nonneg := data.uniformRemainderConstant_nonneg
  integrableProductError := data.integrableProductError
  largeFrequencyBounds := by
    filter_upwards [data.largePrincipalBounds,
      data.beam0.pointwiseRemainder_rate,
      data.beam1.pointwiseRemainder_rate,
      data.beam2.pointwiseRemainder_rate,
      data.beam3.pointwiseRemainder_rate]
      with rho hprincipal h0 h1 h2 h3
    intro x
    have hrateNonneg :
        0 <= sourceBeamRemainderRate (spatialDimension + 1) rho :=
      sourceBeamRemainderRate_nonneg _ _
    have hr0 :
        ‖data.beam0.pointwiseRemainder rho x‖ <=
          data.uniformRemainderConstant *
            sourceBeamRemainderRate (spatialDimension + 1) rho :=
      (h0 x).trans (mul_le_mul_of_nonneg_right
        data.beam0_constant_le_uniform hrateNonneg)
    have hr1 :
        ‖data.beam1.pointwiseRemainder rho x‖ <=
          data.uniformRemainderConstant *
            sourceBeamRemainderRate (spatialDimension + 1) rho :=
      (h1 x).trans (mul_le_mul_of_nonneg_right
        data.beam1_constant_le_uniform hrateNonneg)
    have hr2 :
        ‖data.beam2.pointwiseRemainder rho x‖ <=
          data.uniformRemainderConstant *
            sourceBeamRemainderRate (spatialDimension + 1) rho :=
      (h2 x).trans (mul_le_mul_of_nonneg_right
        data.beam2_constant_le_uniform hrateNonneg)
    have hr3 :
        ‖data.beam3.pointwiseRemainder rho x‖ <=
          data.uniformRemainderConstant *
            sourceBeamRemainderRate (spatialDimension + 1) rho :=
      (h3 x).trans (mul_le_mul_of_nonneg_right
        data.beam3_constant_le_uniform hrateNonneg)
    exact {
      coefficient_le := (hprincipal x).1
      principal0_le := (hprincipal x).2.1
      principal1_le := (hprincipal x).2.2.1
      principal2_le := (hprincipal x).2.2.2.1
      principal3_le := (hprincipal x).2.2.2.2
      remainder0_le := hr0
      remainder1_le := hr1
      remainder2_le := hr2
      remainder3_le := hr3 }

/-- The equation-(3.11) residual estimates therefore generate the scaled
`C * rho^-2` beam-substitution estimate used after equation (4.3). -/
theorem scaledProductError_rate
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    ∀ᶠ rho in atTop,
      ‖data.toBeamProductRemainderData.scaledProductError rho‖ <=
        data.toBeamProductRemainderData.equation44ErrorConstant *
          equation44RemainderRate rho :=
  data.toBeamProductRemainderData.scaledProductError_rate

/-- One certificate exposing all four equation-(3.12) corrections and their
downstream equation-(4.4) product bound. -/
structure Certificate
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) : Prop where
  beam0Equation312 : Equation312RemainderData.Certificate data.beam0
  beam1Equation312 : Equation312RemainderData.Certificate data.beam1
  beam2Equation312 : Equation312RemainderData.Certificate data.beam2
  beam3Equation312 : Equation312RemainderData.Certificate data.beam3
  commonConstantNonnegative : 0 <= data.uniformRemainderConstant
  beamProductCertificate : BeamProductRemainderData.Certificate
    data.toBeamProductRemainderData
  equation44BeamSubstitutionRate : ∀ᶠ rho in atTop,
    ‖data.toBeamProductRemainderData.scaledProductError rho‖ <=
      data.toBeamProductRemainderData.equation44ErrorConstant *
        equation44RemainderRate rho

def certificate
    (data : FourBeamEquation312Data
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      mu spatialDimension beamOrder residualDerivativeOrder) :
    Certificate data where
  beam0Equation312 := data.beam0.certificate
  beam1Equation312 := data.beam1.certificate
  beam2Equation312 := data.beam2.certificate
  beam3Equation312 := data.beam3.certificate
  commonConstantNonnegative := data.uniformRemainderConstant_nonneg
  beamProductCertificate := data.toBeamProductRemainderData.certificate
  equation44BeamSubstitutionRate := data.scaledProductError_rate

end FourBeamEquation312Data

end LiuWang2025SemilinearWaveEquation312EnergyClosure
