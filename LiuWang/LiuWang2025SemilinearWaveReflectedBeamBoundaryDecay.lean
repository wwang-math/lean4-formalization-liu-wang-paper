import LiuWang.LiuWang2025SemilinearWaveGaussianRecovery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Liu--Wang 2025: reflected-beam boundary decay packet

Section 3.2 of Liu--Wang, arXiv:2511.08794v1, matches the incident and
reflected phase jets and chooses opposite boundary amplitudes.  The resulting
beam trace satisfies the paper rate

`rho ^ (-((N - k + 1) / 2 + 3 / 4))`.

This is the displayed source exponent.  The adjacent
`LiuWang2025SemilinearWaveGaussianBoundaryScaling` module audits the change of
variables and shows that `3/4` is the three-transverse-dimensional
specialization of the dimension-correct term `d/4`.

This module verifies the algebraic reflection cancellation and the asymptotic
passage from that quantitative rate to the inaccessible-boundary limit used
in equations (4.5)--(4.6).  In particular, the private platform no longer
needs to accept `boundary -> 0` as a separate terminal hypothesis once a beam
packet supplies the paper's norm estimate.

The geometric construction of the matching phase jets, Riccati solution,
transport hierarchy, Sobolev trace estimate, and the norm bound itself remain
source-specific analytic obligations.
-/

noncomputable section

open Filter Topology

namespace LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay

open LiuWang2025SemilinearWaveGaussianRecovery

/-- Boundary decay exponent in equations (3.14), (3.17), and (4.5). -/
def boundaryDecayExponent (N k : Nat) : Real :=
  ((N : Real) - (k : Real) + 1) / 2 + 3 / 4

/-- The exponent is positive in the derivative range used by the reflected
beam construction. -/
theorem boundaryDecayExponent_pos
    {N k : Nat} (hk : k <= N + 1) :
    0 < boundaryDecayExponent N k := by
  have hkReal : (k : Real) <= (N : Real) + 1 := by
    exact_mod_cast hk
  unfold boundaryDecayExponent
  linarith

/-- Frequency-indexed paper rate.  The value at `rho = 0` is irrelevant to
the high-frequency limit. -/
def boundaryDecayRate (N k : Nat) (rho : Nat) : Real :=
  (rho : Real) ^ (-boundaryDecayExponent N k)

theorem boundaryDecayRate_tendsto_zero
    {N k : Nat} (hk : k <= N + 1) :
    Tendsto (boundaryDecayRate N k) atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop (boundaryDecayExponent_pos hk)).comp
    tendsto_natCast_atTop_atTop

/-- Boundary value of one incident/reflected beam pair. -/
def reflectedBeamTrace
    (rho : Real) (incidentPhase reflectedPhase : Complex)
    (incidentAmplitude reflectedAmplitude : Complex) : Complex :=
  Complex.exp (Complex.I * (rho : Complex) * incidentPhase) *
      incidentAmplitude +
    Complex.exp (Complex.I * (rho : Complex) * reflectedPhase) *
      reflectedAmplitude

/-- Exact decomposition used immediately before equation (3.14). -/
theorem reflectedBeamTrace_decomposition
    (rho : Real) (incidentPhase reflectedPhase : Complex)
    (incidentAmplitude reflectedAmplitude : Complex) :
    reflectedBeamTrace rho incidentPhase reflectedPhase
        incidentAmplitude reflectedAmplitude =
      (Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
          Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)) *
          incidentAmplitude +
        Complex.exp (Complex.I * (rho : Complex) * reflectedPhase) *
          (reflectedAmplitude + incidentAmplitude) := by
  unfold reflectedBeamTrace
  ring

/-- Matching boundary phases and opposite amplitudes cancel the beam trace
exactly.  The paper obtains high-order rather than global exact matching, and
the remainder of the module records the resulting quantitative decay. -/
theorem reflectedBeamTrace_eq_zero_of_exact_matching
    (rho : Real) (phase amplitude : Complex) :
    reflectedBeamTrace rho phase phase amplitude (-amplitude) = 0 := by
  simp [reflectedBeamTrace]

/-- Quantitative two-error form of reflection cancellation. -/
theorem norm_reflectedBeamTrace_le
    (rho : Real) (incidentPhase reflectedPhase : Complex)
    (incidentAmplitude reflectedAmplitude : Complex)
    (phaseMismatch amplitudeMismatch : Real)
    (hphase :
      ‖Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
        Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ <=
          phaseMismatch)
    (hamplitude : ‖reflectedAmplitude + incidentAmplitude‖ <=
      amplitudeMismatch) :
    ‖reflectedBeamTrace rho incidentPhase reflectedPhase
        incidentAmplitude reflectedAmplitude‖ <=
      phaseMismatch * ‖incidentAmplitude‖ +
        ‖Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ *
          amplitudeMismatch := by
  rw [reflectedBeamTrace_decomposition]
  calc
    ‖(Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
          Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)) *
          incidentAmplitude +
        Complex.exp (Complex.I * (rho : Complex) * reflectedPhase) *
          (reflectedAmplitude + incidentAmplitude)‖ <=
      ‖(Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
          Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)) *
          incidentAmplitude‖ +
        ‖Complex.exp (Complex.I * (rho : Complex) * reflectedPhase) *
          (reflectedAmplitude + incidentAmplitude)‖ := norm_add_le _ _
    _ = ‖Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
          Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ *
          ‖incidentAmplitude‖ +
        ‖Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ *
          ‖reflectedAmplitude + incidentAmplitude‖ := by
      rw [norm_mul, norm_mul]
    _ <= phaseMismatch * ‖incidentAmplitude‖ +
        ‖Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ *
          amplitudeMismatch := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hphase (norm_nonneg incidentAmplitude))
        (mul_le_mul_of_nonneg_left hamplitude
          (norm_nonneg
            (Complex.exp (Complex.I * (rho : Complex) * reflectedPhase))))

/-- A reflected beam packet carrying exactly the paper's quantitative
inaccessible-boundary norm estimate. -/
structure BoundaryDecayPacket
    (E : Type*) [SeminormedAddCommGroup E] where
  order : Nat
  derivativeOrder : Nat
  boundaryTrace : Nat -> E
  boundConstant : Real
  derivativeOrder_le : derivativeOrder <= order + 1
  boundConstant_nonneg : 0 <= boundConstant
  norm_boundaryTrace_le : forall rho,
    ‖boundaryTrace rho‖ <=
      boundConstant * boundaryDecayRate order derivativeOrder rho

namespace BoundaryDecayPacket

variable {E : Type*} [SeminormedAddCommGroup E]

theorem exponent_pos (P : BoundaryDecayPacket E) :
    0 < boundaryDecayExponent P.order P.derivativeOrder :=
  boundaryDecayExponent_pos P.derivativeOrder_le

/-- Equation (3.17) supplies the vanishing boundary trace required in (4.5). -/
theorem boundaryTrace_tendsto_zero (P : BoundaryDecayPacket E) :
    Tendsto P.boundaryTrace atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun rho => norm_nonneg (P.boundaryTrace rho))
    P.norm_boundaryTrace_le
  simpa using
    tendsto_const_nhds.mul
      (boundaryDecayRate_tendsto_zero P.derivativeOrder_le)

/-- Cauchy--Schwarz transfers the checked beam rate to the inaccessible
boundary pairing. -/
theorem inaccessibleBoundaryPairing_tendsto_zero
    {F : Type*} [SeminormedAddCommGroup F]
    (P : BoundaryDecayPacket E)
    (pairing : Nat -> F) (fluxNorm : Real)
    (hpairing : forall rho,
      ‖pairing rho‖ <= fluxNorm * ‖P.boundaryTrace rho‖) :
    Tendsto pairing atTop (nhds 0) := by
  exact boundaryPairing_tendsto_zero_of_norm_bound
    pairing (fun rho => ‖P.boundaryTrace rho‖) fluxNorm
    hpairing
    (tendsto_zero_iff_norm_tendsto_zero.mp P.boundaryTrace_tendsto_zero)

end BoundaryDecayPacket

/-- Point-recovery data where boundary convergence is derived from the
paper-rate estimate instead of accepted as a separate limit. -/
structure RatePointRecoveryData where
  coefficient : Complex
  stationaryConstant : Complex
  amplitudeProduct : Complex
  principal : Nat -> Complex
  error : Nat -> Complex
  boundary : Nat -> Complex
  order : Nat
  derivativeOrder : Nat
  boundaryConstant : Real
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  amplitudeProduct_ne_zero : amplitudeProduct ≠ 0
  derivativeOrder_le : derivativeOrder <= order + 1
  boundaryConstant_nonneg : 0 <= boundaryConstant
  principal_tendsto : Tendsto principal atTop
    (nhds (stationaryConstant * coefficient * amplitudeProduct))
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  boundary_rate : forall rho,
    ‖boundary rho‖ <=
      boundaryConstant * boundaryDecayRate order derivativeOrder rho
  integralIdentity : forall rho, principal rho + error rho = boundary rho

namespace RatePointRecoveryData

/-- The rate data produces the older point-recovery packet with its boundary
limit proved. -/
def toPointRecoveryData
    (D : RatePointRecoveryData) : PointRecoveryData where
  coefficient := D.coefficient
  stationaryConstant := D.stationaryConstant
  amplitudeProduct := D.amplitudeProduct
  principal := D.principal
  error := D.error
  boundary := D.boundary
  stationaryConstant_ne_zero := D.stationaryConstant_ne_zero
  amplitudeProduct_ne_zero := D.amplitudeProduct_ne_zero
  principal_tendsto := D.principal_tendsto
  error_tendsto_zero := D.error_tendsto_zero
  inaccessibleBoundary_tendsto_zero := by
    let packet : BoundaryDecayPacket Complex := {
      order := D.order
      derivativeOrder := D.derivativeOrder
      boundaryTrace := D.boundary
      boundConstant := D.boundaryConstant
      derivativeOrder_le := D.derivativeOrder_le
      boundConstant_nonneg := D.boundaryConstant_nonneg
      norm_boundaryTrace_le := D.boundary_rate
    }
    exact packet.boundaryTrace_tendsto_zero
  integralIdentity := D.integralIdentity

/-- Equations (3.17), (4.3), and the stationary-phase limit force the cubic
coefficient to vanish at the selected point. -/
theorem coefficient_eq_zero (D : RatePointRecoveryData) :
    D.coefficient = 0 :=
  D.toPointRecoveryData.coefficient_eq_zero

/-- Product-facing certificate for one source-faithful reflected-beam packet. -/
structure Certificate (D : RatePointRecoveryData) : Prop where
  boundaryExponentPositive :
    0 < boundaryDecayExponent D.order D.derivativeOrder
  inaccessibleBoundaryVanishes : Tendsto D.boundary atTop (nhds 0)
  coefficientZero : D.coefficient = 0

def certificate (D : RatePointRecoveryData) : Certificate D where
  boundaryExponentPositive := boundaryDecayExponent_pos D.derivativeOrder_le
  inaccessibleBoundaryVanishes := D.toPointRecoveryData.inaccessibleBoundary_tendsto_zero
  coefficientZero := D.coefficient_eq_zero

end RatePointRecoveryData

end LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay
