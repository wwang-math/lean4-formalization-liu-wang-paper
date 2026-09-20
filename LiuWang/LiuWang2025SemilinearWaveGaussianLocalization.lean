import LiuWang.LiuWang2025SemilinearWaveGaussianRecovery
import Mathlib.Analysis.Fourier.Inversion

/-!
# Liu--Wang 2025: normalized Gaussian localization for equation (4.4)

The stationary-phase step in equation (4.4) of Liu--Wang isolates the value
of the cubic interaction profile at a selected point.  This module verifies a
finite-dimensional positive-definite Gaussian normal form of that
localization.  The normalized kernels have mass one and converge to the
Dirac mass at the selected point; consequently the principal term converges
to the coefficient times the four beam amplitudes.

Unlike the abstract endpoint in
`LiuWang2025SemilinearWaveGaussianRecovery`, the principal-term limit here is
not supplied as a hypothesis.  It is generated from Mathlib's Gaussian
approximate-identity theorem.  What remains outside this module is the
source-specific geometric reduction from the complex Lorentzian beam phase
and its nondegenerate Hessian to this positive-definite Gaussian normal form,
as well as the quantitative `O(rho^-2)` remainder asserted in the paper.
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped RealInnerProductSpace

namespace LiuWang2025SemilinearWaveGaussianLocalization

open LiuWang2025SemilinearWaveGaussianRecovery

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]

/-- The mass-one Gaussian principal term centered at `point`.  Its
normalization is exactly the one used by Mathlib's Gaussian approximate
identity. -/
def normalizedGaussianPrincipal
    (profile : V -> Complex) (point : V) (c : Real) : Complex :=
  ∫ w : V,
    ((Real.pi * c : Complex) ^
          (Module.finrank Real V / 2 : Complex) *
        Complex.exp
          (-Real.pi ^ 2 * c * ‖point - w‖ ^ 2)) •
      profile w

/-- The continuous-frequency Gaussian principal converges to evaluation of
the interaction profile at the selected point. -/
theorem normalizedGaussianPrincipal_tendsto
    (profile : V -> Complex) (point : V)
    (hprofile : Integrable profile)
    (hcontinuous : ContinuousAt profile point) :
    Tendsto (normalizedGaussianPrincipal profile point) atTop
      (nhds (profile point)) := by
  exact Real.tendsto_integral_gaussian_smul' hprofile hcontinuous

/-- Integer-frequency version used by the Gaussian-beam packets in the
paper. -/
def normalizedGaussianPrincipalNat
    (profile : V -> Complex) (point : V) (rho : Nat) : Complex :=
  normalizedGaussianPrincipal profile point (rho : Real)

theorem normalizedGaussianPrincipalNat_tendsto
    (profile : V -> Complex) (point : V)
    (hprofile : Integrable profile)
    (hcontinuous : ContinuousAt profile point) :
    Tendsto (normalizedGaussianPrincipalNat profile point) atTop
      (nhds (profile point)) := by
  exact (normalizedGaussianPrincipal_tendsto
    profile point hprofile hcontinuous).comp tendsto_natCast_atTop_atTop

/-- Product of the four leading beam amplitudes appearing in equation
(4.4). -/
def amplitudeProductAt
    (a0 a1 a2 a3 : V -> Complex) (point : V) : Complex :=
  a0 point * a1 point * a2 point * a3 point

/-- Cubic interaction profile localized in equation (4.4). -/
def cubicInteractionProfile
    (coefficient a0 a1 a2 a3 : V -> Complex) (x : V) : Complex :=
  coefficient x * a0 x * a1 x * a2 x * a3 x

omit [NormedAddCommGroup V] [InnerProductSpace Real V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V] in
@[simp] theorem cubicInteractionProfile_at
    (coefficient a0 a1 a2 a3 : V -> Complex) (point : V) :
    cubicInteractionProfile coefficient a0 a1 a2 a3 point =
      coefficient point * amplitudeProductAt a0 a1 a2 a3 point := by
  simp [cubicInteractionProfile, amplitudeProductAt, mul_assoc]

/-- Principal term after including the nonzero stationary-phase constant. -/
def scaledGaussianPrincipal
    (stationaryConstant : Complex)
    (coefficient a0 a1 a2 a3 : V -> Complex)
    (point : V) (rho : Nat) : Complex :=
  stationaryConstant *
    normalizedGaussianPrincipalNat
      (cubicInteractionProfile coefficient a0 a1 a2 a3) point rho

/-- Checked Gaussian version of the leading asymptotic in equation (4.4). -/
theorem scaledGaussianPrincipal_tendsto
    (stationaryConstant : Complex)
    (coefficient a0 a1 a2 a3 : V -> Complex)
    (point : V)
    (hprofile : Integrable
      (cubicInteractionProfile coefficient a0 a1 a2 a3))
    (hcontinuous : ContinuousAt
      (cubicInteractionProfile coefficient a0 a1 a2 a3) point) :
    Tendsto
      (scaledGaussianPrincipal stationaryConstant
        coefficient a0 a1 a2 a3 point)
      atTop
      (nhds
        (stationaryConstant * coefficient point *
          amplitudeProductAt a0 a1 a2 a3 point)) := by
  have hlocalize := normalizedGaussianPrincipalNat_tendsto
    (cubicInteractionProfile coefficient a0 a1 a2 a3)
    point hprofile hcontinuous
  simpa [scaledGaussianPrincipal, mul_assoc] using
    (tendsto_const_nhds.mul hlocalize)

/-- Paper-facing data for point recovery when the principal term has been
reduced to the checked normalized Gaussian model.  Only the geometric
normal-form reduction, remainder decay, boundary decay, and the resulting
integral identity are inputs; localization of the leading term is a theorem. -/
structure GaussianPointRecoveryData where
  point : V
  coefficient : V -> Complex
  amplitude0 : V -> Complex
  amplitude1 : V -> Complex
  amplitude2 : V -> Complex
  amplitude3 : V -> Complex
  stationaryConstant : Complex
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  amplitudeProduct_ne_zero :
    amplitudeProductAt amplitude0 amplitude1 amplitude2 amplitude3 point ≠ 0
  interactionProfile_integrable : Integrable
    (cubicInteractionProfile coefficient
      amplitude0 amplitude1 amplitude2 amplitude3)
  interactionProfile_continuousAt : ContinuousAt
    (cubicInteractionProfile coefficient
      amplitude0 amplitude1 amplitude2 amplitude3) point
  error : Nat -> Complex
  boundary : Nat -> Complex
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  inaccessibleBoundary_tendsto_zero : Tendsto boundary atTop (nhds 0)
  integralIdentity : forall rho,
    scaledGaussianPrincipal stationaryConstant coefficient
        amplitude0 amplitude1 amplitude2 amplitude3 point rho +
      error rho = boundary rho

namespace GaussianPointRecoveryData

/-- Forgetful map to the abstract recovery packet.  The crucial
`principal_tendsto` field is synthesized by the Gaussian localization
theorem above rather than accepted from the caller. -/
def toPointRecoveryData (data : GaussianPointRecoveryData (V := V)) :
    PointRecoveryData where
  coefficient := data.coefficient data.point
  stationaryConstant := data.stationaryConstant
  amplitudeProduct := amplitudeProductAt data.amplitude0 data.amplitude1
    data.amplitude2 data.amplitude3 data.point
  principal := scaledGaussianPrincipal data.stationaryConstant
    data.coefficient data.amplitude0 data.amplitude1 data.amplitude2
      data.amplitude3 data.point
  error := data.error
  boundary := data.boundary
  stationaryConstant_ne_zero := data.stationaryConstant_ne_zero
  amplitudeProduct_ne_zero := data.amplitudeProduct_ne_zero
  principal_tendsto := scaledGaussianPrincipal_tendsto
    data.stationaryConstant data.coefficient data.amplitude0 data.amplitude1
      data.amplitude2 data.amplitude3 data.point
      data.interactionProfile_integrable data.interactionProfile_continuousAt
  error_tendsto_zero := data.error_tendsto_zero
  inaccessibleBoundary_tendsto_zero :=
    data.inaccessibleBoundary_tendsto_zero
  integralIdentity := data.integralIdentity

/-- Equation-(4.4) Gaussian localization, a vanishing remainder, and
vanishing inaccessible-boundary leakage force pointwise coefficient
recovery. -/
theorem coefficient_at_point_eq_zero
    (data : GaussianPointRecoveryData (V := V)) :
    data.coefficient data.point = 0 :=
  data.toPointRecoveryData.coefficient_eq_zero

/-- One-object product certificate exposing the generated principal limit,
the boundary limit, and the recovered coefficient value. -/
structure Certificate (data : GaussianPointRecoveryData (V := V)) : Prop where
  principalLimit : Tendsto
    (scaledGaussianPrincipal data.stationaryConstant data.coefficient
      data.amplitude0 data.amplitude1 data.amplitude2 data.amplitude3
      data.point)
    atTop
    (nhds
      (data.stationaryConstant * data.coefficient data.point *
        amplitudeProductAt data.amplitude0 data.amplitude1 data.amplitude2
          data.amplitude3 data.point))
  boundaryLimit : Tendsto data.boundary atTop (nhds 0)
  coefficientZero : data.coefficient data.point = 0

def certificate (data : GaussianPointRecoveryData (V := V)) :
    Certificate data where
  principalLimit := scaledGaussianPrincipal_tendsto
    data.stationaryConstant data.coefficient data.amplitude0 data.amplitude1
      data.amplitude2 data.amplitude3 data.point
      data.interactionProfile_integrable data.interactionProfile_continuousAt
  boundaryLimit := data.inaccessibleBoundary_tendsto_zero
  coefficientZero := data.coefficient_at_point_eq_zero

end GaussianPointRecoveryData

end LiuWang2025SemilinearWaveGaussianLocalization
