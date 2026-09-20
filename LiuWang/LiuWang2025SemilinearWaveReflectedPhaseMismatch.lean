import LiuWang.LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Liu--Wang 2025: quantitative reflected-phase mismatch

This module verifies the pointwise exponential estimate used between equations
(3.13) and (3.16) of arXiv:2511.08794v1.  A high-order mismatch of the incident
and reflected phases is combined with coercivity of the imaginary reflected
phase.  Lean derives the Gaussian suppression of the oscillatory-exponential
difference instead of accepting it as a generic phase-error bound.

The theorem is local and source-faithful: its `q` is the quadratic transverse
coercivity quantity (in the paper, a constant times `|y|^2`), while
`phaseJetBound` is supplied by the matched boundary jets.  Constructing those
jets from the reflected Lorentzian geometry and integrating the pointwise
estimate into the full Sobolev boundary norm remain separate obligations.
-/

noncomputable section

open Complex

namespace LiuWang2025SemilinearWaveReflectedPhaseMismatch

open LiuWang2025SemilinearWaveReflectedBeamBoundaryDecay

/-- A global exponential difference estimate obtained by factoring at the
second exponential.  This is the analytic replacement for an informal
complex mean-value estimate. -/
theorem norm_exp_sub_exp_le (z w : Complex) :
    ‖Complex.exp z - Complex.exp w‖ ≤
      ‖Complex.exp w‖ * ‖z - w‖ * Real.exp ‖z - w‖ := by
  have hfactor :
      Complex.exp z - Complex.exp w =
        Complex.exp w * (Complex.exp (z - w) - 1) := by
    rw [mul_sub_one, ← Complex.exp_add]
    ring_nf
  have htail :
      ‖Complex.exp (z - w) - 1‖ ≤
        ‖z - w‖ * Real.exp ‖z - w‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (z - w) 1
  rw [hfactor, norm_mul]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left htail (norm_nonneg (Complex.exp w))

/-- The real part of the oscillatory exponent is the negative imaginary
phase. -/
@[simp] theorem oscillatoryExponent_re (rho : Real) (phase : Complex) :
    (Complex.I * (rho : Complex) * phase).re = -rho * phase.im := by
  simp

/-- Scaling the phase difference by `i rho` scales its norm by `rho` when
`rho` is nonnegative. -/
theorem norm_oscillatoryExponent_sub
    {rho : Real} (hrho : 0 ≤ rho) (incidentPhase reflectedPhase : Complex) :
    ‖Complex.I * (rho : Complex) * incidentPhase -
        Complex.I * (rho : Complex) * reflectedPhase‖ =
      rho * ‖incidentPhase - reflectedPhase‖ := by
  have hfactor :
      Complex.I * (rho : Complex) * incidentPhase -
          Complex.I * (rho : Complex) * reflectedPhase =
        Complex.I * (rho : Complex) * (incidentPhase - reflectedPhase) := by
    ring
  rw [hfactor, norm_mul, norm_mul]
  simp [Real.norm_eq_abs, abs_of_nonneg hrho]

/-- Source-facing form of the estimate after equations (3.13) and (3.15).

If the reflected phase has imaginary part at least `q`, while the phase
mismatch has norm at most both `q/2` and `phaseJetBound`, then the difference
of the two oscillatory exponentials has a Gaussian factor
`exp (-(rho*q)/2)`. -/
theorem norm_oscillatoryExp_sub_le_gaussian
    {rho q phaseJetBound : Real}
    {incidentPhase reflectedPhase : Complex}
    (hrho : 0 ≤ rho)
    (hreflectedCoercive : q ≤ reflectedPhase.im)
    (hmismatchAbsorb : ‖incidentPhase - reflectedPhase‖ ≤ q / 2)
    (hmismatchJet : ‖incidentPhase - reflectedPhase‖ ≤ phaseJetBound) :
    ‖Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
        Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ ≤
      rho * phaseJetBound * Real.exp (-(rho * q) / 2) := by
  let d : Real := ‖incidentPhase - reflectedPhase‖
  have hd : 0 ≤ d := norm_nonneg _
  have hphaseJetBound : 0 ≤ phaseJetBound := hd.trans hmismatchJet
  have hscaledNorm :
      ‖Complex.I * (rho : Complex) * incidentPhase -
          Complex.I * (rho : Complex) * reflectedPhase‖ = rho * d := by
    simpa [d] using
      norm_oscillatoryExponent_sub hrho incidentPhase reflectedPhase
  have hexponent :
      -rho * reflectedPhase.im + rho * d ≤ -(rho * q) / 2 := by
    have hdq : d ≤ q / 2 := by simpa [d] using hmismatchAbsorb
    nlinarith
  have hexp :
      Real.exp (-rho * reflectedPhase.im) * Real.exp (rho * d) ≤
        Real.exp (-(rho * q) / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent
  calc
    ‖Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
        Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ ≤
      ‖Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ *
        ‖Complex.I * (rho : Complex) * incidentPhase -
          Complex.I * (rho : Complex) * reflectedPhase‖ *
        Real.exp
          ‖Complex.I * (rho : Complex) * incidentPhase -
            Complex.I * (rho : Complex) * reflectedPhase‖ :=
      norm_exp_sub_exp_le _ _
    _ = rho * d *
        (Real.exp (-rho * reflectedPhase.im) * Real.exp (rho * d)) := by
      rw [Complex.norm_exp, oscillatoryExponent_re, hscaledNorm]
      ring
    _ ≤ rho * d * Real.exp (-(rho * q) / 2) := by
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hrho hd)
    _ ≤ rho * phaseJetBound * Real.exp (-(rho * q) / 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmismatchJet hrho)
        (Real.exp_nonneg _)

/-- The reflected exponential itself obeys the stronger unhalved Gaussian
bound. -/
theorem norm_reflectedExp_le_gaussian
    {rho q : Real} {reflectedPhase : Complex}
    (hrho : 0 ≤ rho) (hreflectedCoercive : q ≤ reflectedPhase.im) :
    ‖Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ ≤
      Real.exp (-(rho * q)) := by
  rw [Complex.norm_exp, oscillatoryExponent_re]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Quantitative pointwise reflected-trace cancellation.  This packages the
phase-difference estimate with the exact incident/reflected decomposition
already verified by the platform. -/
theorem norm_reflectedBeamTrace_le_gaussian
    {rho q phaseJetBound amplitudeJetBound : Real}
    {incidentPhase reflectedPhase incidentAmplitude reflectedAmplitude : Complex}
    (hrho : 0 ≤ rho)
    (hreflectedCoercive : q ≤ reflectedPhase.im)
    (hmismatchAbsorb : ‖incidentPhase - reflectedPhase‖ ≤ q / 2)
    (hmismatchJet : ‖incidentPhase - reflectedPhase‖ ≤ phaseJetBound)
    (hamplitudeJet : ‖reflectedAmplitude + incidentAmplitude‖ ≤
      amplitudeJetBound) :
    ‖reflectedBeamTrace rho incidentPhase reflectedPhase
        incidentAmplitude reflectedAmplitude‖ ≤
      rho * phaseJetBound * Real.exp (-(rho * q) / 2) *
          ‖incidentAmplitude‖ +
        Real.exp (-(rho * q)) * amplitudeJetBound := by
  apply (norm_reflectedBeamTrace_le rho incidentPhase reflectedPhase
    incidentAmplitude reflectedAmplitude
    (rho * phaseJetBound * Real.exp (-(rho * q) / 2))
    amplitudeJetBound
    (norm_oscillatoryExp_sub_le_gaussian hrho hreflectedCoercive
      hmismatchAbsorb hmismatchJet)
    hamplitudeJet).trans
  have hamplitudeJetBound : 0 ≤ amplitudeJetBound :=
    (norm_nonneg (reflectedAmplitude + incidentAmplitude)).trans hamplitudeJet
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (norm_reflectedExp_le_gaussian hrho hreflectedCoercive)
    hamplitudeJetBound)

/-- Product-facing certificate for the source's local reflected-phase
cancellation mechanism. -/
structure Certificate : Prop where
  exponentialDifference :
    ∀ {rho q phaseJetBound : Real}
      {incidentPhase reflectedPhase : Complex},
      0 ≤ rho → q ≤ reflectedPhase.im →
      ‖incidentPhase - reflectedPhase‖ ≤ q / 2 →
      ‖incidentPhase - reflectedPhase‖ ≤ phaseJetBound →
      ‖Complex.exp (Complex.I * (rho : Complex) * incidentPhase) -
          Complex.exp (Complex.I * (rho : Complex) * reflectedPhase)‖ ≤
        rho * phaseJetBound * Real.exp (-(rho * q) / 2)
  reflectedTrace :
    ∀ {rho q phaseJetBound amplitudeJetBound : Real}
      {incidentPhase reflectedPhase incidentAmplitude reflectedAmplitude : Complex},
      0 ≤ rho → q ≤ reflectedPhase.im →
      ‖incidentPhase - reflectedPhase‖ ≤ q / 2 →
      ‖incidentPhase - reflectedPhase‖ ≤ phaseJetBound →
      ‖reflectedAmplitude + incidentAmplitude‖ ≤ amplitudeJetBound →
      ‖reflectedBeamTrace rho incidentPhase reflectedPhase
          incidentAmplitude reflectedAmplitude‖ ≤
        rho * phaseJetBound * Real.exp (-(rho * q) / 2) *
            ‖incidentAmplitude‖ +
          Real.exp (-(rho * q)) * amplitudeJetBound

def certificate : Certificate where
  exponentialDifference := fun hrho hcoercive habsorb hjet =>
    norm_oscillatoryExp_sub_le_gaussian hrho hcoercive habsorb hjet
  reflectedTrace := fun hrho hcoercive habsorb hphase hamp =>
    norm_reflectedBeamTrace_le_gaussian hrho hcoercive habsorb hphase hamp

end LiuWang2025SemilinearWaveReflectedPhaseMismatch
