import LiuWang.LiuWang2025SemilinearWaveChartWKB

/-!
# Liu-Wang semilinear wave: the finite-order beam residual in a chart

Section 3.1 of Liu-Wang takes the amplitude

`a_rho = sum_{k=0}^{N} rho^{-k} b_k`

and imposes, on the geodesic and through transverse order `N`, the eikonal
equation `S phi = 0`, the leading transport equation `T b_0 = 0`, and the
hierarchy `- i T b_k + Box_g b_{k-1} = 0`.  The displayed consequence is that
the beam satisfies `Box_g v_rho = O(rho^{-N})`, the surviving term being
`rho^{-N} Box_g b_N`.

This file derives that *exactly*, from the assembled identity of
`LiuWang2025SemilinearWaveChartWKB`.  The three cancellations are hypotheses on
the constructed coefficients -- never on the conclusion -- and the whole
expansion telescopes, leaving only the terminal term.  The residual is a
theorem; it is not stored in a structure.

## Sign convention

`waveOp_beam` produces `waveOp a + w * transportTerm + w^2 * a * eikonalSymbol`
with `w` the complex frequency.  At `w = i rho` the hierarchy condition that
makes the expansion telescope is therefore
`i * transportTerm (b (k+1)) + waveOp (b k) = 0`, which is the source's
`- i T b_k + Box_g b_{k-1} = 0` under the signature convention recorded in the
`ChartWKB` module docstring.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartBeamResidual

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet

variable {n : Nat}

/-! ## Finite combinations of amplitude jets -/

/-- A finite complex-coefficient combination of chart jets, with its derivative
data assembled from the summands. -/
def combo (c : Nat -> Complex) (b : Nat -> ChartJet n) (N : Nat) : ChartJet n where
  val := fun x => ∑ k ∈ Finset.range (N + 1), c k * (b k).val x
  d := fun j x => ∑ k ∈ Finset.range (N + 1), c k * (b k).d j x
  d2 := fun j k x => ∑ m ∈ Finset.range (N + 1), c m * (b m).d2 j k x
  hasDeriv := by
    intro j x
    show HasDerivAt
      (fun t : Real => ∑ k ∈ Finset.range (N + 1), c k * (b k).val (x + t • dir j)) _ 0
    exact HasDerivAt.fun_sum fun k _ => ((b k).hasDeriv j x).const_mul (c k)
  hasDeriv2 := by
    intro j k x
    show HasDerivAt
      (fun t : Real => ∑ m ∈ Finset.range (N + 1), c m * (b m).d k (x + t • dir j)) _ 0
    exact HasDerivAt.fun_sum fun m _ => ((b m).hasDeriv2 j k x).const_mul (c m)

@[simp] theorem combo_val (c : Nat -> Complex) (b : Nat -> ChartJet n) (N : Nat)
    (x : Fin n -> Real) :
    (combo c b N).val x = ∑ k ∈ Finset.range (N + 1), c k * (b k).val x := rfl

@[simp] theorem combo_d (c : Nat -> Complex) (b : Nat -> ChartJet n) (N : Nat)
    (j : Fin n) (x : Fin n -> Real) :
    (combo c b N).d j x = ∑ k ∈ Finset.range (N + 1), c k * (b k).d j x := rfl

@[simp] theorem combo_d2 (c : Nat -> Complex) (b : Nat -> ChartJet n) (N : Nat)
    (j k : Fin n) (x : Fin n -> Real) :
    (combo c b N).d2 j k x = ∑ m ∈ Finset.range (N + 1), c m * (b m).d2 j k x := rfl

variable (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
  (B : Fin n -> (Fin n -> Real) -> Complex)

/-- Swapping a coefficient sum out of a doubly indexed sum. -/
theorem sum_swap_double (x : Fin n -> Real) (c : Nat -> Complex)
    (g : Nat -> Fin n -> Fin n -> Complex) (N : Nat) :
    (∑ j, ∑ k, A j k x * ∑ m ∈ Finset.range (N + 1), c m * g m j k)
      = ∑ m ∈ Finset.range (N + 1), c m * ∑ j, ∑ k, A j k x * g m j k := by
  calc (∑ j, ∑ k, A j k x * ∑ m ∈ Finset.range (N + 1), c m * g m j k)
      = ∑ j, ∑ k, ∑ m ∈ Finset.range (N + 1), A j k x * (c m * g m j k) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ m ∈ Finset.range (N + 1), ∑ k, A j k x * (c m * g m j k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ m ∈ Finset.range (N + 1), ∑ j, ∑ k, A j k x * (c m * g m j k) :=
        Finset.sum_comm
    _ = ∑ m ∈ Finset.range (N + 1), c m * ∑ j, ∑ k, A j k x * g m j k := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- Swapping a coefficient sum out of a singly indexed sum. -/
theorem sum_swap_single (x : Fin n -> Real) (c : Nat -> Complex)
    (g : Nat -> Fin n -> Complex) (N : Nat) :
    (∑ j, B j x * ∑ m ∈ Finset.range (N + 1), c m * g m j)
      = ∑ m ∈ Finset.range (N + 1), c m * ∑ j, B j x * g m j := by
  calc (∑ j, B j x * ∑ m ∈ Finset.range (N + 1), c m * g m j)
      = ∑ j, ∑ m ∈ Finset.range (N + 1), B j x * (c m * g m j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.range (N + 1), ∑ j, B j x * (c m * g m j) := Finset.sum_comm
    _ = ∑ m ∈ Finset.range (N + 1), c m * ∑ j, B j x * g m j := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **The operator is linear in the amplitude.** -/
theorem waveOp_combo (c : Nat -> Complex) (b : Nat -> ChartJet n) (N : Nat)
    (x : Fin n -> Real) :
    waveOp A B (combo c b N) x
      = ∑ m ∈ Finset.range (N + 1), c m * waveOp A B (b m) x := by
  simp only [waveOp, combo_d, combo_d2]
  rw [sum_swap_double A x c (fun m j k => (b m).d2 j k x) N,
    sum_swap_single B x c (fun m j => (b m).d j x) N,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **The transport expression is linear in the amplitude.** -/
theorem transportTerm_combo (phi : ChartJet n) (c : Nat -> Complex)
    (b : Nat -> ChartJet n) (N : Nat) (x : Fin n -> Real) :
    transportTerm A B phi (combo c b N) x
      = ∑ m ∈ Finset.range (N + 1), c m * transportTerm A B phi (b m) x := by
  have hfirst : (∑ j, ∑ k, A j k x
        * ((∑ m ∈ Finset.range (N + 1), c m * (b m).d j x) * phi.d k x
          + (∑ m ∈ Finset.range (N + 1), c m * (b m).d k x) * phi.d j x))
      = ∑ m ∈ Finset.range (N + 1), c m
          * ∑ j, ∑ k, A j k x * ((b m).d j x * phi.d k x + (b m).d k x * phi.d j x) := by
    rw [← sum_swap_double A x c
      (fun m j k => (b m).d j x * phi.d k x + (b m).d k x * phi.d j x) N]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [transportTerm, combo_d, combo_val]
  rw [hfirst, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-! ## The truncated amplitude and the terminal residual -/

/-- The source's truncated amplitude `sum_{k=0}^N rho^{-k} b_k`. -/
def truncatedAmplitude (rho : Real) (b : Nat -> ChartJet n) (N : Nat) : ChartJet n :=
  combo (fun k => ((rho : Complex))⁻¹ ^ k) b N

/-- **The finite-order residual.**  With the eikonal symbol vanishing, the
leading transport expression vanishing, and the hierarchy holding through order
`N`, the whole expansion telescopes and the operator applied to the beam leaves
exactly the source's terminal term `rho^{-N} Box_g b_N`, times the beam's
exponential.  Nothing about the size of the residual is assumed. -/
theorem waveOp_beam_eq_terminal (rho : Real) (hrho : (rho : Complex) ≠ 0)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat) (x : Fin n -> Real)
    (heik : eikonalSymbol A phi x = 0)
    (htrans0 : transportTerm A B phi (b 0) x = 0)
    (hhier : ∀ m ∈ Finset.range N,
      Complex.I * transportTerm A B phi (b (m + 1)) x + waveOp A B (b m) x = 0) :
    waveOp A B (beam (Complex.I * (rho : Complex)) phi (truncatedAmplitude rho b N)) x
      = Complex.exp (Complex.I * (rho : Complex) * phi.val x)
          * (((rho : Complex))⁻¹ ^ N * waveOp A B (b N) x) := by
  rw [waveOp_beam A B, truncatedAmplitude, waveOp_combo A B, transportTerm_combo A B,
    heik, mul_zero, add_zero]
  congr 1
  rw [Finset.mul_sum, Finset.sum_range_succ
      (fun k => ((rho : Complex))⁻¹ ^ k * waveOp A B (b k) x) N,
    Finset.sum_range_succ'
      (fun k => Complex.I * (rho : Complex)
        * (((rho : Complex))⁻¹ ^ k * transportTerm A B phi (b k) x)) N,
    htrans0, mul_zero, mul_zero, add_zero]
  have hzero : (∑ m ∈ Finset.range N,
        ((rho : Complex))⁻¹ ^ m * waveOp A B (b m) x)
      + (∑ m ∈ Finset.range N, Complex.I * (rho : Complex)
          * (((rho : Complex))⁻¹ ^ (m + 1) * transportTerm A B phi (b (m + 1)) x))
      = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun m hm => ?_
    have h := hhier m hm
    have hc : Complex.I * (rho : Complex) * (((rho : Complex))⁻¹ ^ (m + 1))
        = ((rho : Complex))⁻¹ ^ m * Complex.I := by
      rw [pow_succ]
      field_simp
    have hterm : Complex.I * (rho : Complex)
          * (((rho : Complex))⁻¹ ^ (m + 1) * transportTerm A B phi (b (m + 1)) x)
        = ((rho : Complex))⁻¹ ^ m * (Complex.I * transportTerm A B phi (b (m + 1)) x) := by
      calc Complex.I * (rho : Complex)
            * (((rho : Complex))⁻¹ ^ (m + 1) * transportTerm A B phi (b (m + 1)) x)
          = (Complex.I * (rho : Complex) * (((rho : Complex))⁻¹ ^ (m + 1)))
              * transportTerm A B phi (b (m + 1)) x := by ring
        _ = (((rho : Complex))⁻¹ ^ m * Complex.I)
              * transportTerm A B phi (b (m + 1)) x := by rw [hc]
        _ = ((rho : Complex))⁻¹ ^ m
              * (Complex.I * transportTerm A B phi (b (m + 1)) x) := by ring
    rw [hterm]
    linear_combination (((rho : Complex))⁻¹ ^ m) * h
  linear_combination hzero

end LiuWang2025SemilinearWaveChartBeamResidual
