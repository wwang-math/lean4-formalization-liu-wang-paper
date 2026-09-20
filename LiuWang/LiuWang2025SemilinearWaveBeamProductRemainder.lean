import LiuWang.LiuWang2025SemilinearWaveEquation44QuantitativeRecovery

/-!
# Liu--Wang 2025: source beam-product remainder for equation (4.4)

The four exact Gaussian beams used after equation (4.3) have the form
`principal + remainder`.  The paper records a uniform `O(1)` bound for the
principal beams and the source estimate

`remainder = O(rho^(-spaceTimeDimension / 2 - 2))`.

After the interaction integral is multiplied by
`rho^(spaceTimeDimension / 2)`, every term in the difference between the
exact four-beam product and the four-principal-beam product is therefore
`O(rho^-2)`.  This module verifies that implication.  It checks the exact
four-factor telescoping identity, the pointwise norm estimate, the
finite-measure integral estimate, and the exponent cancellation producing
the equation-(4.4) rate.

The analytic construction of the Gaussian beams and the PDE estimate that
supplies the source remainder bound remain geometric/PDE inputs.  The
passage from those inputs to the `O(rho^-2)` interaction error is a theorem.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace LiuWang2025SemilinearWaveBeamProductRemainder

open LiuWang2025SemilinearWaveEquation44QuantitativeRecovery
open LiuWang2025SemilinearWaveGaussianLocalization
open LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay

/-- The source remainder rate from equation (3.12), written using the
space-time dimension rather than the spatial dimension. -/
def sourceBeamRemainderRate (spaceTimeDimension rho : Nat) : Real :=
  (rho : Real) ^
    (-((spaceTimeDimension : Real) / 2 + 2))

/-- The normalization multiplying the four-beam interaction integral. -/
def interactionScale (spaceTimeDimension rho : Nat) : Real :=
  (rho : Real) ^ ((spaceTimeDimension : Real) / 2)

theorem sourceBeamRemainderRate_nonneg
    (spaceTimeDimension rho : Nat) :
    0 <= sourceBeamRemainderRate spaceTimeDimension rho := by
  exact Real.rpow_nonneg (Nat.cast_nonneg rho) _

theorem sourceBeamRemainderRate_le_one
    (spaceTimeDimension rho : Nat) (hrho : 1 <= rho) :
    sourceBeamRemainderRate spaceTimeDimension rho <= 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hrho
  · exact neg_nonpos.mpr
      (add_nonneg
        (div_nonneg (Nat.cast_nonneg spaceTimeDimension) (by norm_num))
        (by norm_num))

theorem interactionScale_nonneg
    (spaceTimeDimension rho : Nat) :
    0 <= interactionScale spaceTimeDimension rho := by
  exact Real.rpow_nonneg (Nat.cast_nonneg rho) _

/-- The exponent calculation behind the paper's `O(rho^-2)` term. -/
theorem interactionScale_mul_sourceBeamRemainderRate
    (spaceTimeDimension rho : Nat) (hrho : 0 < rho) :
    interactionScale spaceTimeDimension rho *
        sourceBeamRemainderRate spaceTimeDimension rho =
      equation44RemainderRate rho := by
  have hrhoReal : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
  rw [interactionScale, sourceBeamRemainderRate, equation44RemainderRate]
  rw [← Real.rpow_add hrhoReal]
  congr 1
  ring

/-- Algebraic telescoping of a product of four exact beams.  Each summand on
the right contains exactly one registered remainder; all later factors are
kept as exact beams. -/
theorem fourBeamProduct_sub_principalProduct
    (v0 v1 v2 v3 r0 r1 r2 r3 : Complex) :
    (v0 + r0) * (v1 + r1) * (v2 + r2) * (v3 + r3) -
        v0 * v1 * v2 * v3 =
      r0 * (v1 + r1) * (v2 + r2) * (v3 + r3) +
        v0 * r1 * (v2 + r2) * (v3 + r3) +
        v0 * v1 * r2 * (v3 + r3) +
        v0 * v1 * v2 * r3 := by
  ring

/-- Pointwise bounds matching the four source Gaussian-beam estimates. -/
structure FourBeamPointwiseBounds
    (coefficient v0 v1 v2 v3 r0 r1 r2 r3 : Complex)
    (coefficientBound principalBound remainderBound : Real) : Prop where
  coefficient_le : ‖coefficient‖ <= coefficientBound
  principal0_le : ‖v0‖ <= principalBound
  principal1_le : ‖v1‖ <= principalBound
  principal2_le : ‖v2‖ <= principalBound
  principal3_le : ‖v3‖ <= principalBound
  remainder0_le : ‖r0‖ <= remainderBound
  remainder1_le : ‖r1‖ <= remainderBound
  remainder2_le : ‖r2‖ <= remainderBound
  remainder3_le : ‖r3‖ <= remainderBound

namespace FourBeamPointwiseBounds

theorem fullBeam_le
    {principalBound remainderBound : Real}
    {v r : Complex}
    (hv : ‖v‖ <= principalBound) (hr : ‖r‖ <= remainderBound) :
    ‖v + r‖ <= principalBound + remainderBound := by
  exact (norm_add_le v r).trans (add_le_add hv hr)

/-- A source-facing four-beam product estimate. -/
theorem coefficient_mul_product_error_le
    {coefficient v0 v1 v2 v3 r0 r1 r2 r3 : Complex}
    {coefficientBound principalBound remainderBound : Real}
    (bounds : FourBeamPointwiseBounds coefficient v0 v1 v2 v3
      r0 r1 r2 r3 coefficientBound principalBound remainderBound)
    (hcoefficient : 0 <= coefficientBound)
    (hprincipal : 0 <= principalBound)
    (hremainder : 0 <= remainderBound) :
    ‖coefficient *
        ((v0 + r0) * (v1 + r1) * (v2 + r2) * (v3 + r3) -
          v0 * v1 * v2 * v3)‖ <=
      4 * coefficientBound * remainderBound *
        (principalBound + remainderBound) ^ 3 := by
  let envelope := principalBound + remainderBound
  have henvelope : 0 <= envelope := add_nonneg hprincipal hremainder
  have hv0 : ‖v0‖ <= envelope := bounds.principal0_le.trans
    (le_add_of_nonneg_right hremainder)
  have hv1 : ‖v1‖ <= envelope := bounds.principal1_le.trans
    (le_add_of_nonneg_right hremainder)
  have hv2 : ‖v2‖ <= envelope := bounds.principal2_le.trans
    (le_add_of_nonneg_right hremainder)
  have hw1 : ‖v1 + r1‖ <= envelope :=
    fullBeam_le
      bounds.principal1_le bounds.remainder1_le
  have hw2 : ‖v2 + r2‖ <= envelope :=
    fullBeam_le
      bounds.principal2_le bounds.remainder2_le
  have hw3 : ‖v3 + r3‖ <= envelope :=
    fullBeam_le
      bounds.principal3_le bounds.remainder3_le
  let term0 := r0 * (v1 + r1) * (v2 + r2) * (v3 + r3)
  let term1 := v0 * r1 * (v2 + r2) * (v3 + r3)
  let term2 := v0 * v1 * r2 * (v3 + r3)
  let term3 := v0 * v1 * v2 * r3
  have hterm0 : ‖term0‖ <= remainderBound * envelope ^ 3 := by
    dsimp [term0]
    simp only [norm_mul]
    calc
      ‖r0‖ * ‖v1 + r1‖ * ‖v2 + r2‖ * ‖v3 + r3‖ <=
          remainderBound * envelope * envelope * envelope := by
        gcongr
        exact bounds.remainder0_le
      _ = remainderBound * envelope ^ 3 := by ring
  have hterm1 : ‖term1‖ <= remainderBound * envelope ^ 3 := by
    dsimp [term1]
    simp only [norm_mul]
    calc
      ‖v0‖ * ‖r1‖ * ‖v2 + r2‖ * ‖v3 + r3‖ <=
          envelope * remainderBound * envelope * envelope := by
        gcongr
        exact bounds.remainder1_le
      _ = remainderBound * envelope ^ 3 := by ring
  have hterm2 : ‖term2‖ <= remainderBound * envelope ^ 3 := by
    dsimp [term2]
    simp only [norm_mul]
    calc
      ‖v0‖ * ‖v1‖ * ‖r2‖ * ‖v3 + r3‖ <=
          envelope * envelope * remainderBound * envelope := by
        gcongr
        exact bounds.remainder2_le
      _ = remainderBound * envelope ^ 3 := by ring
  have hterm3 : ‖term3‖ <= remainderBound * envelope ^ 3 := by
    dsimp [term3]
    simp only [norm_mul]
    calc
      ‖v0‖ * ‖v1‖ * ‖v2‖ * ‖r3‖ <=
          envelope * envelope * envelope * remainderBound := by
        gcongr
        exact bounds.remainder3_le
      _ = remainderBound * envelope ^ 3 := by ring
  have hsum : ‖term0 + term1 + term2 + term3‖ <=
      4 * (remainderBound * envelope ^ 3) := by
    have h01 := norm_add_le term0 term1
    have h012 := norm_add_le (term0 + term1) term2
    have h0123 := norm_add_le (term0 + term1 + term2) term3
    calc
      ‖term0 + term1 + term2 + term3‖ <=
          ‖term0‖ + ‖term1‖ + ‖term2‖ + ‖term3‖ := by
        linarith
      _ <= 4 * (remainderBound * envelope ^ 3) := by linarith
  rw [fourBeamProduct_sub_principalProduct]
  change ‖coefficient * (term0 + term1 + term2 + term3)‖ <= _
  rw [norm_mul]
  calc
    ‖coefficient‖ * ‖term0 + term1 + term2 + term3‖ <=
        coefficientBound * (4 * (remainderBound * envelope ^ 3)) := by
      gcongr
      exact bounds.coefficient_le
    _ = 4 * coefficientBound * remainderBound *
        (principalBound + remainderBound) ^ 3 := by
      dsimp [envelope]
      ring

end FourBeamPointwiseBounds

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Paper-facing source data for the product remainder.  The asymptotic
field is exactly the collection of estimates used in the substitution after
equation (4.3), before stationary phase is applied. -/
structure BeamProductRemainderData (mu : Measure Omega) where
  spaceTimeDimension : Nat
  coefficient : Omega -> Complex
  principal0 : Nat -> Omega -> Complex
  principal1 : Nat -> Omega -> Complex
  principal2 : Nat -> Omega -> Complex
  principal3 : Nat -> Omega -> Complex
  remainder0 : Nat -> Omega -> Complex
  remainder1 : Nat -> Omega -> Complex
  remainder2 : Nat -> Omega -> Complex
  remainder3 : Nat -> Omega -> Complex
  coefficientBound : Real
  principalBound : Real
  remainderConstant : Real
  coefficientBound_nonneg : 0 <= coefficientBound
  principalBound_nonneg : 0 <= principalBound
  remainderConstant_nonneg : 0 <= remainderConstant
  integrableProductError : forall rho, Integrable (fun x =>
    coefficient x *
      ((principal0 rho x + remainder0 rho x) *
          (principal1 rho x + remainder1 rho x) *
          (principal2 rho x + remainder2 rho x) *
          (principal3 rho x + remainder3 rho x) -
        principal0 rho x * principal1 rho x *
          principal2 rho x * principal3 rho x)) mu
  largeFrequencyBounds : ∀ᶠ rho in atTop, forall x,
    FourBeamPointwiseBounds
      (coefficient x)
      (principal0 rho x) (principal1 rho x)
      (principal2 rho x) (principal3 rho x)
      (remainder0 rho x) (remainder1 rho x)
      (remainder2 rho x) (remainder3 rho x)
      coefficientBound principalBound
      (remainderConstant *
        sourceBeamRemainderRate spaceTimeDimension rho)

namespace BeamProductRemainderData

variable {mu : Measure Omega} [IsFiniteMeasure mu]

def productErrorIntegrand (data : BeamProductRemainderData mu)
    (rho : Nat) (x : Omega) : Complex :=
  data.coefficient x *
    ((data.principal0 rho x + data.remainder0 rho x) *
        (data.principal1 rho x + data.remainder1 rho x) *
        (data.principal2 rho x + data.remainder2 rho x) *
        (data.principal3 rho x + data.remainder3 rho x) -
      data.principal0 rho x * data.principal1 rho x *
        data.principal2 rho x * data.principal3 rho x)

def scaledProductError (data : BeamProductRemainderData mu)
    (rho : Nat) : Complex :=
  (interactionScale data.spaceTimeDimension rho : Complex) *
    (∫ x, data.productErrorIntegrand rho x ∂mu)

/-- Explicit constant in the generated equation-(4.4) error bound. -/
def equation44ErrorConstant (data : BeamProductRemainderData mu) : Real :=
  4 * data.coefficientBound * data.remainderConstant *
    (data.principalBound + data.remainderConstant) ^ 3 *
    mu.real Set.univ

omit [IsFiniteMeasure mu] in
theorem equation44ErrorConstant_nonneg
    (data : BeamProductRemainderData mu) :
    0 <= data.equation44ErrorConstant := by
  unfold equation44ErrorConstant
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) data.coefficientBound_nonneg
      · exact data.remainderConstant_nonneg
    · exact pow_nonneg
        (add_nonneg data.principalBound_nonneg
          data.remainderConstant_nonneg) _
  · exact measureReal_nonneg

/-- The source beam estimates generate the paper's uniform
`C * rho^-2` interaction-error estimate. -/
theorem scaledProductError_rate
    (data : BeamProductRemainderData mu) :
    ∀ᶠ rho in atTop,
      ‖data.scaledProductError rho‖ <=
        data.equation44ErrorConstant * equation44RemainderRate rho := by
  have hrhoLarge : ∀ᶠ rho : Nat in atTop, 1 <= rho :=
    eventually_ge_atTop 1
  filter_upwards [data.largeFrequencyBounds, hrhoLarge] with rho bounds hrho
  have hsourceNonneg :
      0 <= sourceBeamRemainderRate data.spaceTimeDimension rho :=
    sourceBeamRemainderRate_nonneg _ _
  have hsourceLeOne :
      sourceBeamRemainderRate data.spaceTimeDimension rho <= 1 :=
    sourceBeamRemainderRate_le_one _ _ hrho
  have hremainderBoundNonneg :
      0 <= data.remainderConstant *
        sourceBeamRemainderRate data.spaceTimeDimension rho :=
    mul_nonneg data.remainderConstant_nonneg hsourceNonneg
  have hremainderBoundLe :
      data.remainderConstant *
          sourceBeamRemainderRate data.spaceTimeDimension rho <=
        data.remainderConstant := by
    simpa using mul_le_mul_of_nonneg_left hsourceLeOne
      data.remainderConstant_nonneg
  have hpointwise : forall x,
      ‖data.productErrorIntegrand rho x‖ <=
        (4 * data.coefficientBound * data.remainderConstant *
          (data.principalBound + data.remainderConstant) ^ 3) *
          sourceBeamRemainderRate data.spaceTimeDimension rho := by
    intro x
    have hraw := (bounds x).coefficient_mul_product_error_le
      data.coefficientBound_nonneg data.principalBound_nonneg
      hremainderBoundNonneg
    change ‖data.productErrorIntegrand rho x‖ <= _
    calc
      ‖data.productErrorIntegrand rho x‖ <=
          4 * data.coefficientBound *
            (data.remainderConstant *
              sourceBeamRemainderRate data.spaceTimeDimension rho) *
            (data.principalBound +
              data.remainderConstant *
                sourceBeamRemainderRate data.spaceTimeDimension rho) ^ 3 := hraw
      _ <= 4 * data.coefficientBound *
            (data.remainderConstant *
              sourceBeamRemainderRate data.spaceTimeDimension rho) *
            (data.principalBound + data.remainderConstant) ^ 3 := by
          gcongr
          · exact mul_nonneg
              (mul_nonneg (by norm_num) data.coefficientBound_nonneg)
              hremainderBoundNonneg
          · exact add_nonneg data.principalBound_nonneg
              hremainderBoundNonneg
      _ = (4 * data.coefficientBound * data.remainderConstant *
            (data.principalBound + data.remainderConstant) ^ 3) *
            sourceBeamRemainderRate data.spaceTimeDimension rho := by ring
  have hintegral :
      ‖∫ x, data.productErrorIntegrand rho x ∂mu‖ <=
        ((4 * data.coefficientBound * data.remainderConstant *
          (data.principalBound + data.remainderConstant) ^ 3) *
          sourceBeamRemainderRate data.spaceTimeDimension rho) *
          mu.real Set.univ := by
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall hpointwise)
  have hscaleNonneg :
      0 <= interactionScale data.spaceTimeDimension rho :=
    interactionScale_nonneg _ _
  have hrhoPos : 0 < rho := lt_of_lt_of_le Nat.zero_lt_one hrho
  rw [scaledProductError, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hscaleNonneg]
  calc
    interactionScale data.spaceTimeDimension rho *
        ‖∫ x, data.productErrorIntegrand rho x ∂mu‖ <=
      interactionScale data.spaceTimeDimension rho *
        (((4 * data.coefficientBound * data.remainderConstant *
          (data.principalBound + data.remainderConstant) ^ 3) *
          sourceBeamRemainderRate data.spaceTimeDimension rho) *
          mu.real Set.univ) :=
      mul_le_mul_of_nonneg_left hintegral hscaleNonneg
    _ = data.equation44ErrorConstant * equation44RemainderRate rho := by
      rw [equation44ErrorConstant,
        ← interactionScale_mul_sourceBeamRemainderRate
          data.spaceTimeDimension rho hrhoPos]
      ring

/-- Product-facing certificate for the newly generated source estimate. -/
structure Certificate (data : BeamProductRemainderData mu) : Prop where
  sourceRemainderRateNonnegative : forall rho,
    0 <= sourceBeamRemainderRate data.spaceTimeDimension rho
  scalingLaw : forall rho, 0 < rho ->
    interactionScale data.spaceTimeDimension rho *
        sourceBeamRemainderRate data.spaceTimeDimension rho =
      equation44RemainderRate rho
  errorConstantNonnegative : 0 <= data.equation44ErrorConstant
  equation44RateBound : ∀ᶠ rho in atTop,
    ‖data.scaledProductError rho‖ <=
      data.equation44ErrorConstant * equation44RemainderRate rho

def certificate (data : BeamProductRemainderData mu) : Certificate data where
  sourceRemainderRateNonnegative :=
    sourceBeamRemainderRate_nonneg data.spaceTimeDimension
  scalingLaw := interactionScale_mul_sourceBeamRemainderRate
    data.spaceTimeDimension
  errorConstantNonnegative := data.equation44ErrorConstant_nonneg
  equation44RateBound := data.scaledProductError_rate

end BeamProductRemainderData

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]

/-- Equation-(4.4) recovery data separating the generated four-beam product
error from the stationary-phase expansion error.  The first rate is proved
by `BeamProductRemainderData.scaledProductError_rate`; only the genuinely
microlocal stationary-phase rate remains an analytic input. -/
structure BeamGeneratedEquation44RecoveryData
    (mu : Measure V) [IsFiniteMeasure mu] where
  beamData : BeamProductRemainderData mu
  point : V
  amplitude0 : V -> Complex
  amplitude1 : V -> Complex
  amplitude2 : V -> Complex
  amplitude3 : V -> Complex
  stationaryConstant : Complex
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  amplitudeProduct_ne_zero :
    amplitudeProductAt amplitude0 amplitude1 amplitude2 amplitude3 point ≠ 0
  interactionProfile_integrable : Integrable
    (cubicInteractionProfile beamData.coefficient
      amplitude0 amplitude1 amplitude2 amplitude3)
  interactionProfile_continuousAt : ContinuousAt
    (cubicInteractionProfile beamData.coefficient
      amplitude0 amplitude1 amplitude2 amplitude3) point
  stationaryPhaseError : Nat -> Complex
  stationaryPhaseErrorConstant : Real
  stationaryPhaseErrorConstant_nonneg : 0 <= stationaryPhaseErrorConstant
  stationaryPhaseError_rate : ∀ᶠ rho in atTop,
    ‖stationaryPhaseError rho‖ <=
      stationaryPhaseErrorConstant * equation44RemainderRate rho
  boundaryPacket : BoundaryDecayPacket Complex
  integralIdentity : forall rho,
    scaledGaussianPrincipal stationaryConstant beamData.coefficient
        amplitude0 amplitude1 amplitude2 amplitude3 point rho +
      (beamData.scaledProductError rho + stationaryPhaseError rho) =
        boundaryPacket.boundaryTrace rho

namespace BeamGeneratedEquation44RecoveryData

variable {mu : Measure V} [IsFiniteMeasure mu]

/-- Total equation-(4.4) error, with the beam-substitution and
stationary-phase contributions kept separately visible. -/
def totalEquation44Error (data : BeamGeneratedEquation44RecoveryData mu)
    (rho : Nat) : Complex :=
  data.beamData.scaledProductError rho + data.stationaryPhaseError rho

def totalEquation44ErrorConstant
    (data : BeamGeneratedEquation44RecoveryData mu) : Real :=
  data.beamData.equation44ErrorConstant + data.stationaryPhaseErrorConstant

theorem totalEquation44ErrorConstant_nonneg
    (data : BeamGeneratedEquation44RecoveryData mu) :
    0 <= data.totalEquation44ErrorConstant :=
  add_nonneg data.beamData.equation44ErrorConstant_nonneg
    data.stationaryPhaseErrorConstant_nonneg

/-- The generated beam-product rate and the source stationary-phase rate
combine to the exact equation-(4.4) `C * rho^-2` bound. -/
theorem totalEquation44Error_rate
    (data : BeamGeneratedEquation44RecoveryData mu) :
    ∀ᶠ rho in atTop,
      ‖data.totalEquation44Error rho‖ <=
        data.totalEquation44ErrorConstant * equation44RemainderRate rho := by
  filter_upwards [data.beamData.scaledProductError_rate,
    data.stationaryPhaseError_rate] with rho hbeam hphase
  calc
    ‖data.totalEquation44Error rho‖ <=
        ‖data.beamData.scaledProductError rho‖ +
          ‖data.stationaryPhaseError rho‖ :=
      norm_add_le _ _
    _ <= data.beamData.equation44ErrorConstant *
          equation44RemainderRate rho +
        data.stationaryPhaseErrorConstant *
          equation44RemainderRate rho :=
      add_le_add hbeam hphase
    _ = data.totalEquation44ErrorConstant *
          equation44RemainderRate rho := by
      rw [totalEquation44ErrorConstant]
      ring

/-- Adapter to the quantitative equation-(4.4) recovery packet.  The
beam-product part of the error and its constant are generated, then combined
with the separately tracked stationary-phase error. -/
def toQuantitativeEquation44RecoveryData
    (data : BeamGeneratedEquation44RecoveryData mu) :
    QuantitativeEquation44RecoveryData (V := V) where
  point := data.point
  coefficient := data.beamData.coefficient
  amplitude0 := data.amplitude0
  amplitude1 := data.amplitude1
  amplitude2 := data.amplitude2
  amplitude3 := data.amplitude3
  stationaryConstant := data.stationaryConstant
  stationaryConstant_ne_zero := data.stationaryConstant_ne_zero
  amplitudeProduct_ne_zero := data.amplitudeProduct_ne_zero
  interactionProfile_integrable := data.interactionProfile_integrable
  interactionProfile_continuousAt := data.interactionProfile_continuousAt
  error := data.totalEquation44Error
  errorBoundConstant := data.totalEquation44ErrorConstant
  errorBoundConstant_nonneg := data.totalEquation44ErrorConstant_nonneg
  error_rate := data.totalEquation44Error_rate
  boundaryPacket := data.boundaryPacket
  integralIdentity := data.integralIdentity

/-- Source-generated equation-(4.4) coefficient-recovery endpoint. -/
theorem coefficient_at_point_eq_zero
    (data : BeamGeneratedEquation44RecoveryData mu) :
    data.beamData.coefficient data.point = 0 :=
  data.toQuantitativeEquation44RecoveryData.coefficient_at_point_eq_zero

/-- Product certificate retaining both the beam-product estimate and the
downstream point-recovery certificate. -/
structure Certificate
    (data : BeamGeneratedEquation44RecoveryData mu) : Prop where
  productErrorIntegrable : forall rho,
    Integrable (data.beamData.productErrorIntegrand rho) mu
  beamProductEstimate : BeamProductRemainderData.Certificate data.beamData
  stationaryPhaseRate : ∀ᶠ rho in atTop,
    ‖data.stationaryPhaseError rho‖ <=
      data.stationaryPhaseErrorConstant * equation44RemainderRate rho
  totalErrorRate : ∀ᶠ rho in atTop,
    ‖data.totalEquation44Error rho‖ <=
      data.totalEquation44ErrorConstant * equation44RemainderRate rho
  quantitativeRecovery : QuantitativeEquation44RecoveryData.Certificate
    data.toQuantitativeEquation44RecoveryData
  coefficientZero : data.beamData.coefficient data.point = 0

def certificate (data : BeamGeneratedEquation44RecoveryData mu) :
    Certificate data where
  productErrorIntegrable := by
    intro rho
    simpa [BeamProductRemainderData.productErrorIntegrand] using
      data.beamData.integrableProductError rho
  beamProductEstimate := data.beamData.certificate
  stationaryPhaseRate := data.stationaryPhaseError_rate
  totalErrorRate := data.totalEquation44Error_rate
  quantitativeRecovery := data.toQuantitativeEquation44RecoveryData.certificate
  coefficientZero := data.coefficient_at_point_eq_zero

end BeamGeneratedEquation44RecoveryData

end LiuWang2025SemilinearWaveBeamProductRemainder
