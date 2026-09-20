import LiuWang.LiuWang2025SemilinearWaveChartBeamResidual

/-!
# Liu-Wang semilinear wave: the unconditional WKB expansion

`LiuWang2025SemilinearWaveChartBeamResidual.waveOp_beam_eq_terminal` telescopes
the WKB sum under the hypothesis that the eikonal symbol, the leading transport
expression and the hierarchy vanish *at the chart point*.  The source does not
achieve that: it only kills the transverse Taylor jets at `z' = 0` through order
`N`, so away from the central ray each of those three expressions is a Taylor
remainder, not zero.

This file removes the hypotheses entirely.  `waveOp_beam_expand` is an
*identity*, valid at every chart point with no assumption beyond `rho /= 0`: it
sorts the WKB sum into

* the leading transport expression `T b_0`, carrying one power of the frequency;
* the hierarchy expressions `i T b_{m+1} + Box_g b_m`, `m < N`, carrying
  `rho^{-m}`;
* the terminal `rho^{-N} Box_g b_N`;
* the eikonal symbol, carrying `rho^2` times the truncated amplitude.

Under the source's jet conditions the first three groups are the Taylor
remainders and the last is the eikonal remainder; setting them to zero recovers
the earlier telescoping theorem exactly (`waveOp_beam_eq_terminal_of_expand`).

Nothing here is an estimate, so nothing here can hide one.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartBeamAssembly

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamResidual

variable {n : Nat}
variable (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
  (B : Fin n -> (Fin n -> Real) -> Complex)

/-- The source's hierarchy expression at step `m`.  Under the source's jet
conditions its transverse jet vanishes through order `N` at `z' = 0`; in
general it is whatever it is. -/
def hierarchyExpr (phi : ChartJet n) (b : Nat -> ChartJet n) (m : Nat)
    (x : Fin n -> Real) : Complex :=
  Complex.I * transportTerm A B phi (b (m + 1)) x + waveOp A B (b m) x

/-- Shifting one frequency power across the hierarchy index. -/
theorem freq_shift (rho : Real) (hrho : (rho : Complex) ≠ 0) (m : Nat)
    (z : Complex) :
    Complex.I * (rho : Complex) * (((rho : Complex))⁻¹ ^ (m + 1) * z)
      = ((rho : Complex))⁻¹ ^ m * (Complex.I * z) := by
  have hc : Complex.I * (rho : Complex) * (((rho : Complex))⁻¹ ^ (m + 1))
      = ((rho : Complex))⁻¹ ^ m * Complex.I := by
    rw [pow_succ]
    field_simp
  calc Complex.I * (rho : Complex) * (((rho : Complex))⁻¹ ^ (m + 1) * z)
      = (Complex.I * (rho : Complex) * (((rho : Complex))⁻¹ ^ (m + 1))) * z := by ring
    _ = (((rho : Complex))⁻¹ ^ m * Complex.I) * z := by rw [hc]
    _ = ((rho : Complex))⁻¹ ^ m * (Complex.I * z) := by ring

/-- **The unconditional WKB expansion.**  No cancellation is assumed: every
surviving term of the source's construction appears explicitly, with its own
power of the frequency. -/
theorem waveOp_beam_expand (rho : Real) (hrho : (rho : Complex) ≠ 0)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat) (x : Fin n -> Real) :
    waveOp A B (beam (Complex.I * (rho : Complex)) phi (truncatedAmplitude rho b N)) x
      = Complex.exp (Complex.I * (rho : Complex) * phi.val x)
        * (Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x
            + (∑ m ∈ Finset.range N,
                ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x)
            + ((rho : Complex))⁻¹ ^ N * waveOp A B (b N) x
            - (rho : Complex) ^ 2 * (truncatedAmplitude rho b N).val x
                * eikonalSymbol A phi x) := by
  rw [waveOp_beam_freq A B, truncatedAmplitude, waveOp_combo A B,
    transportTerm_combo A B]
  congr 1
  have hkey :
      (∑ m ∈ Finset.range (N + 1),
          ((rho : Complex))⁻¹ ^ m * waveOp A B (b m) x)
        + Complex.I * (rho : Complex)
            * (∑ m ∈ Finset.range (N + 1),
                ((rho : Complex))⁻¹ ^ m * transportTerm A B phi (b m) x)
      = Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x
          + (∑ m ∈ Finset.range N,
              ((rho : Complex))⁻¹ ^ m
                * (Complex.I * transportTerm A B phi (b (m + 1)) x
                    + waveOp A B (b m) x))
          + ((rho : Complex))⁻¹ ^ N * waveOp A B (b N) x := by
    rw [Finset.sum_range_succ
        (fun k => ((rho : Complex))⁻¹ ^ k * waveOp A B (b k) x) N,
      Finset.sum_range_succ'
        (fun k => ((rho : Complex))⁻¹ ^ k * transportTerm A B phi (b k) x) N,
      mul_add, Finset.mul_sum]
    have hterm : ∀ m ∈ Finset.range N,
        Complex.I * (rho : Complex)
            * (((rho : Complex))⁻¹ ^ (m + 1) * transportTerm A B phi (b (m + 1)) x)
          = ((rho : Complex))⁻¹ ^ m
              * (Complex.I * transportTerm A B phi (b (m + 1)) x) :=
      fun m _ => freq_shift rho hrho m _
    rw [Finset.sum_congr rfl hterm]
    have hzero : ((rho : Complex))⁻¹ ^ 0 = 1 := pow_zero _
    rw [hzero, one_mul]
    have hmerge :
        (∑ m ∈ Finset.range N, ((rho : Complex))⁻¹ ^ m * waveOp A B (b m) x)
          + (∑ m ∈ Finset.range N, ((rho : Complex))⁻¹ ^ m
              * (Complex.I * transportTerm A B phi (b (m + 1)) x))
        = ∑ m ∈ Finset.range N, ((rho : Complex))⁻¹ ^ m
            * (Complex.I * transportTerm A B phi (b (m + 1)) x
                + waveOp A B (b m) x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    linear_combination hmerge
  simp only [hierarchyExpr]
  linear_combination hkey

/-- The earlier telescoping theorem, recovered from the unconditional
expansion by setting the three jet expressions to zero.  This confirms that the
expansion is a strict generalization and that no term was dropped. -/
theorem waveOp_beam_eq_terminal_of_expand (rho : Real) (hrho : (rho : Complex) ≠ 0)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat) (x : Fin n -> Real)
    (heik : eikonalSymbol A phi x = 0)
    (htrans0 : transportTerm A B phi (b 0) x = 0)
    (hhier : ∀ m ∈ Finset.range N, hierarchyExpr A B phi b m x = 0) :
    waveOp A B (beam (Complex.I * (rho : Complex)) phi (truncatedAmplitude rho b N)) x
      = Complex.exp (Complex.I * (rho : Complex) * phi.val x)
          * (((rho : Complex))⁻¹ ^ N * waveOp A B (b N) x) := by
  rw [waveOp_beam_expand A B rho hrho phi b N x, heik, htrans0,
    Finset.sum_congr rfl (fun m hm => by rw [hhier m hm, mul_zero])]
  simp

end LiuWang2025SemilinearWaveChartBeamAssembly
