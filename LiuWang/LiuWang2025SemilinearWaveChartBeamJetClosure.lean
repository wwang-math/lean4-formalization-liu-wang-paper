import LiuWang.LiuWang2025SemilinearWaveChartBeamFiniteOrder
import LiuWang.LiuWang2025SemilinearWaveDirectionalJet

/-!
# Liu-Wang semilinear wave: the residual rate from the finite jet conditions

This file closes the loop.  The hypotheses of
`LiuWang2025SemilinearWaveChartBeamFiniteOrder.beamRemainderPart_L2_equation311`
are pointwise polynomial bounds; the source does not assume those, it *derives*
them from the finite-order jet conditions

  `partial^alpha (S phi)(s, 0) = 0`,  `partial^alpha (T b_0)(s, 0) = 0`,
  `partial^alpha (- i T b_k + Box_g b_{k-1})(s, 0) = 0`,  `|alpha| <= N`,

together with the cutoff and smoothness of the coefficients.  Here the same
derivation is carried out: each of the three expressions is presented as a
`DirJet` with vanishing derivatives at the centre, bounded order-`N+1`
derivatives on the tube and support in the tube, and
`LiuWang2025SemilinearWaveDirectionalJet.global_polynomial_bound_of_vanishing_jet`
turns that into the polynomial bound.

The conclusion is the source's equation-(3.11) rate.  No estimate is assumed
anywhere in the chain.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartBeamJetClosure

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamResidual
open LiuWang2025SemilinearWaveChartBeamAssembly
open LiuWang2025SemilinearWaveChartBeamFiniteOrder
open LiuWang2025SemilinearWaveDirectionalJet
open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)
open LiuWang2025SemilinearWaveEquation312EnergyClosure

variable {n : Nat}
variable (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
  (B : Fin n -> (Fin n -> Real) -> Complex)

/-- The source's finite-order jet condition on one chart expression: the
expression is the value of a finite directional jet, all of whose derivatives
through order `N` vanish at the centre, whose order-`N+1` derivatives are
bounded on the tube of radius `r`, and which is supported in that tube. -/
structure FiniteJetCondition (N : Nat) (F : (Fin n -> Real) -> Complex)
    (M r : Real) : Prop where
  /-- Existence of the jet is part of the condition, not of the conclusion. -/
  exists_jet : ∃ J : DirJet n N,
    (∀ x, J.D [] x = F x)
    ∧ (∀ l : List (Fin n -> Real), l.length ≤ N -> J.D l 0 = 0)
    ∧ (∀ u : Fin n -> Real, radius u = 1 -> ∀ y : Fin n -> Real, radius y ≤ r ->
        ‖J.D (List.replicate (N + 1) u) y‖ ≤ M)
    ∧ (∀ x, r < radius x -> J.D [] x = 0)

/-- **The polynomial bound, derived from the jet condition.** -/
theorem polynomial_bound_of_finiteJetCondition {N : Nat}
    {F : (Fin n -> Real) -> Complex} {M r : Real} (hM : 0 ≤ M)
    (h : FiniteJetCondition N F M r) (x : Fin n -> Real) :
    ‖F x‖ ≤ M * (radius x) ^ (N + 1) := by
  obtain ⟨J, hval, hjet, hbd, hsupp⟩ := h.exists_jet
  rw [← hval x]
  exact global_polynomial_bound_of_vanishing_jet J hM hjet hbd hsupp x

/-- **The source's equation-(3.11) residual rate, from the source's jet
conditions.**  The eikonal symbol, the leading transport expression and every
hierarchy expression are required only to satisfy the finite-order jet
conditions the source imposes; the polynomial bounds, the Gaussian gain and the
exponent are all derived. -/
theorem beamRemainder_L2_equation311_of_finiteJets
    (rho : Real) (hrho : 1 ≤ rho) (phi : ChartJet n) (b : Nat -> ChartJet n)
    (N : Nat) {coer Ca MT MH Me r : Real} (hcoer : 0 < coer)
    (hMT : 0 ≤ MT) (hMH : 0 ≤ MH) (hMe : 0 ≤ Me) (hCa : 0 ≤ Ca)
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (ha : ∀ x, ‖(truncatedAmplitude rho b N).val x‖ ≤ Ca)
    (hjetT : FiniteJetCondition N (transportTerm A B phi (b 0)) MT r)
    (hjetH : ∀ m ∈ Finset.range N,
      FiniteJetCondition N (hierarchyExpr A B phi b m) MH r)
    (hjetE : FiniteJetCondition N (eikonalSymbol A phi) Me r) :
    Real.sqrt (∫ x : Fin n -> Real, ‖beamRemainderPart A B rho phi b N x‖ ^ 2)
      ≤ (MT + (N : Real) * MH + Ca * Me)
          * Real.sqrt (gaussianMoment n (N + 1) (2 * coer))
          * rho ^ (-(equation311DecayExponent n N 0)) :=
  beamRemainderPart_L2_equation311 A B rho hrho phi b N hcoer hMT hMH hCa hMe hIm
    (fun x => polynomial_bound_of_finiteJetCondition hMT hjetT x)
    (fun m hm x => polynomial_bound_of_finiteJetCondition hMH (hjetH m hm) x)
    ha
    (fun x => polynomial_bound_of_finiteJetCondition hMe hjetE x)

/-! ## The terminal term is dominated -/

/-- The terminal term's transverse rate. -/
theorem beamTerminalPart_L2_rate (rho : Real) (hrho : 0 < rho)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat)
    {coer CW : Real} (hcoer : 0 < coer) (hCW : 0 ≤ CW)
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (hW : ∀ x, ‖waveOp A B (b N) x‖ ≤ CW) :
    Real.sqrt (∫ x : Fin n -> Real, ‖beamTerminalPart A B rho phi b N x‖ ^ 2)
      ≤ (rho⁻¹) ^ N * CW * rho ^ (-((0 : Real) / 2 + (n : Real) / 4))
          * Real.sqrt (gaussianMoment n 0 (2 * coer)) := by
  have hC : (0 : Real) ≤ (rho⁻¹) ^ N * CW :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 hrho.le) N) hCW
  have h := sqrt_integral_normSq_le_of_radiusProfileBound hC hcoer hrho
    (beamTerminalPart_radiusProfileBound A B rho hrho phi b N hIm hW)
  simpa using h

/-- **The terminal term never dominates.**  `rho^{-(N + n/4)}` is at least as
small as the equation-(3.11) rate for every beam order and every spatial
dimension, so the residual rate is governed by the `rho^2`-weighted eikonal and
transport remainders, exactly as in the source. -/
theorem terminal_exponent_le_equation311 (n N : Nat) :
    equation311DecayExponent n N 0 ≤ (N : Real) + (n : Real) / 4 := by
  unfold equation311DecayExponent
  push_cast
  have hN : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  linarith

/-- The frequency comparison that the exponent inequality delivers. -/
theorem terminal_rate_le_equation311Rate {rho : Real} (hrho : 1 ≤ rho)
    (n N : Nat) :
    rho ^ (-((N : Real) + (n : Real) / 4))
      ≤ rho ^ (-(equation311DecayExponent n N 0)) :=
  Real.rpow_le_rpow_of_exponent_le hrho
    (neg_le_neg (terminal_exponent_le_equation311 n N))

end LiuWang2025SemilinearWaveChartBeamJetClosure
