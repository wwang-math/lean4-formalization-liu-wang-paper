import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Liu--Wang semilinear-wave higher-order linearization

This module formalizes the algebraic and inductive core of Boya Liu and
Weinan Wang, *On a partial data inverse problem for the semi-linear wave
equation*, arXiv:2511.08794.

The paper assumes that the nonlinearity starts at cubic order.  Third-order
linearization of `V_3 u^3 / 3!` must therefore produce exactly
`V_3 w1 w2 w3`; missing the factorial or one inclusion-exclusion term changes
the recovered coefficient.  Lean verifies that cancellation below.  It also
checks the strong induction used to recover every coefficient of order at
least three and the final formal-power-series extensionality step.

The differentiability of the nonlinear solution map and the PDE equations
satisfied by its derivatives are analytic inputs, not consequences of these
polynomial identities.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveLinearization

/-- Three-variable inclusion-exclusion operator applied to the cubic
monomial.  This is the finite-difference form of the mixed third derivative
at the zero background. -/
def cubicMixedDifference (w1 w2 w3 : Complex) : Complex :=
  (w1 + w2 + w3) ^ 3 -
    (w1 + w2) ^ 3 -
    (w1 + w3) ^ 3 -
    (w2 + w3) ^ 3 +
    w1 ^ 3 + w2 ^ 3 + w3 ^ 3

/-- Exact cubic polarization: all pure and repeated-index terms cancel, and
the six permutations of the mixed product remain. -/
theorem cubicMixedDifference_eq_six_mul
    (w1 w2 w3 : Complex) :
    cubicMixedDifference w1 w2 w3 = 6 * w1 * w2 * w3 := by
  simp [cubicMixedDifference]
  ring

/-- The paper's `1 / 3!` normalization cancels the six mixed permutations. -/
theorem cubic_factorial_normalization
    (w1 w2 w3 : Complex) :
    cubicMixedDifference w1 w2 w3 /
        (Nat.factorial 3 : Complex) =
      w1 * w2 * w3 := by
  rw [cubicMixedDifference_eq_six_mul]
  norm_num [Nat.factorial]
  ring

/-- With the unknown cubic coefficient included, third-order linearization
produces precisely the source term used in the paper. -/
theorem cubic_coefficient_mixed_response
    (V3 w1 w2 w3 : Complex) :
    V3 *
        (cubicMixedDifference w1 w2 w3 /
          (Nat.factorial 3 : Complex)) =
      V3 * w1 * w2 * w3 := by
  rw [cubic_factorial_normalization]
  ring

/-- Full scalar third-jet product-rule numerator for `u^3`.  The variables
`u12`, `u13`, `u23`, and `u123` are arbitrary higher derivatives of the
nonlinear solution map; keeping them here prevents the cubic calculation
from silently replacing the nonlinear solution by its first-order part. -/
def cubicThirdJetDerivative
    (u0 u1 u2 u3 u12 u13 u23 u123 : Complex) : Complex :=
  6 * u1 * u2 * u3 +
    6 * u0 * (u12 * u3 + u13 * u2 + u23 * u1) +
    3 * u0 ^ 2 * u123

/-- Since the zero-boundary, zero-initial-data background solution is zero,
all terms containing second and third solution derivatives disappear after
division by `3!`.  The remaining source is exactly `w1*w2*w3`. -/
theorem cubicThirdJetDerivative_factorial_at_zero
    (w1 w2 w3 u12 u13 u23 u123 : Complex) :
    cubicThirdJetDerivative 0 w1 w2 w3 u12 u13 u23 u123 /
        (Nat.factorial 3 : Complex) =
      w1 * w2 * w3 := by
  norm_num [cubicThirdJetDerivative, Nat.factorial]
  ring

/-- Coefficient-bearing form of the source identity in equation (the third
linearized wave equation) of Liu--Wang. -/
theorem cubicThirdJet_coefficient_response_at_zero
    (V3 w1 w2 w3 u12 u13 u23 u123 : Complex) :
    V3 *
        (cubicThirdJetDerivative 0 w1 w2 w3 u12 u13 u23 u123 /
          (Nat.factorial 3 : Complex)) =
      V3 * w1 * w2 * w3 := by
  rw [cubicThirdJetDerivative_factorial_at_zero]
  ring

/-- Strong-induction engine for the recovery of `V_m`, `m >= 4`, after the
cubic coefficient has been recovered.  The step hypothesis exposes exactly
which lower coefficients it consumes. -/
theorem higherCoefficientRecovery_induction
    {Coefficient : Type*}
    (V1 V2 : Nat -> Coefficient)
    (hcubic : V1 3 = V2 3)
    (hstep : forall m, 4 <= m ->
      (forall k, 3 <= k -> k < m -> V1 k = V2 k) ->
      V1 m = V2 m) :
    forall m, 3 <= m -> V1 m = V2 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm
      by_cases hm3 : m = 3
      · simpa [hm3] using hcubic
      · have h3lt : 3 < m := lt_of_le_of_ne hm (Ne.symm hm3)
        have hm4 : 4 <= m := Nat.succ_le_iff.mpr h3lt
        exact hstep m hm4 (fun k hk3 hkm => ih k hkm hk3)

/-- Equality of all Taylor coefficients determines the formal nonlinearity.
This is the algebraic endpoint underlying the paper's final use of the
holomorphic power-series expansion. -/
theorem powerSeries_eq_of_coeff_eq
    (V1 V2 : PowerSeries Complex)
    (hcoeff : forall m,
      PowerSeries.coeff m V1 = PowerSeries.coeff m V2) :
    V1 = V2 := by
  ext m
  exact hcoeff m

/-- Complete coefficient-recovery induction for a nonlinearity whose
coefficients of order zero, one, and two are already fixed. -/
theorem powerSeries_eq_of_cubic_and_higher_recovery
    (V1 V2 : PowerSeries Complex)
    (hlow : forall m, m < 3 ->
      PowerSeries.coeff m V1 = PowerSeries.coeff m V2)
    (hcubic : PowerSeries.coeff 3 V1 = PowerSeries.coeff 3 V2)
    (hstep : forall m, 4 <= m ->
      (forall k, 3 <= k -> k < m ->
        PowerSeries.coeff k V1 = PowerSeries.coeff k V2) ->
      PowerSeries.coeff m V1 = PowerSeries.coeff m V2) :
    V1 = V2 := by
  apply powerSeries_eq_of_coeff_eq
  intro m
  by_cases hm : m < 3
  · exact hlow m hm
  · have hm3 : 3 <= m := Nat.le_of_not_gt hm
    exact higherCoefficientRecovery_induction
      (fun k => PowerSeries.coeff k V1)
      (fun k => PowerSeries.coeff k V2)
      hcubic hstep m hm3

/-- Compact certificate for the checked algebraic portion of the paper's
higher-order linearization route. -/
structure HigherOrderLinearizationCertificate : Prop where
  cubicPolarization : forall w1 w2 w3 : Complex,
    cubicMixedDifference w1 w2 w3 = 6 * w1 * w2 * w3
  cubicNormalization : forall w1 w2 w3 : Complex,
    cubicMixedDifference w1 w2 w3 /
        (Nat.factorial 3 : Complex) =
      w1 * w2 * w3
  zeroBackgroundThirdJet : forall w1 w2 w3 u12 u13 u23 u123 : Complex,
    cubicThirdJetDerivative 0 w1 w2 w3 u12 u13 u23 u123 /
        (Nat.factorial 3 : Complex) =
      w1 * w2 * w3

/-- The algebraic certificate is generated with no paper-specific analytic
hypothesis. -/
def higherOrderLinearizationCertificate :
    HigherOrderLinearizationCertificate where
  cubicPolarization := cubicMixedDifference_eq_six_mul
  cubicNormalization := cubic_factorial_normalization
  zeroBackgroundThirdJet := cubicThirdJetDerivative_factorial_at_zero

end LiuWang2025SemilinearWaveLinearization
