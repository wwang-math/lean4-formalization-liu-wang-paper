import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Fin

/-!
# Liu-Wang semilinear wave: the WKB identity in a local coordinate chart

Section 3.1 of Liu-Wang writes, in Fermi coordinates around a null geodesic,

`Box_g (e^{i rho phi} a_rho)
   = e^{i rho phi} [ rho^2 (S phi) a_rho - i rho (T a_rho) + Box_g a_rho ]`

with `S phi = <d phi, d phi>_g` and `T a = 2 <d phi, d a>_g - (Box_g phi) a`.
Every later step of the construction -- the eikonal jet equations, the transport
hierarchy, and the finite-order residual -- is read off from that one identity.

This file proves it, in a genuine finite-dimensional local chart with *variable*
coefficients.  Nothing is assumed about the phase or the amplitude beyond the
existence of their first and second directional derivatives, which are carried
as data in the manner of `LiuWang2025SemilinearWaveConcreteDirectedGreen`; the
identity itself is a theorem.

## What is exposed

* `ChartJet n` : a function on the chart `Fin n -> Real` together with its first
  and second directional derivatives along the coordinate directions, and the
  `HasDerivAt` witnesses relating them.  No smoothness beyond second order is
  requested, and none is hidden.
* `waveOp A B` : a second-order operator with *variable* coefficients
  `A : Fin n -> Fin n -> (Fin n -> Real) -> Complex` and
  `B : Fin n -> (Fin n -> Real) -> Complex`.  In the source's situation
  `A = g^{-1}` and `B` collects the first-order terms of
  `|g|^{-1/2} d_j (g^{jk} |g|^{1/2} d_k .)`; no positivity or symmetry is needed
  for the identity.
* `eikonalSymbol A phi` : the source's `S phi = <d phi, d phi>_g`.
* `transportTerm A B phi a` : the source's transport expression
  `2 <d phi, d a>_g + (Box_g phi) a`, written for a general `A`.
* `beam w phi a` : the beam `a e^{w phi}`, with its derivative data
  *constructed*, not postulated.
* `waveOp_beam` : the assembled identity, for an arbitrary complex frequency
  `w`; `waveOp_beam_freq` specialises it to `w = i rho`, which is the displayed
  form of the source with the signature convention made explicit.

## Sign convention

The source writes `Box_g = d_t^2 - Delta_g` and `S phi = <d phi, d phi>_g`, so
its `Box_g` is `-g^{jk} d_j d_k` up to first order terms.  Here `A` is the
coefficient of `d_j d_k` in `waveOp` directly, so the specialisation
`waveOp_beam_freq` carries `- rho^2` where the source displays `+ rho^2`; the
two agree once `A` is taken to be `-g^{-1}`.  The convention is stated rather
than silently absorbed.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartWKB

variable {n : Nat}

/-- The `j`-th coordinate direction of the chart. -/
def dir (j : Fin n) : Fin n -> Real := Pi.single j 1

@[simp] theorem add_zero_smul_dir (x : Fin n -> Real) (j : Fin n) :
    x + (0 : Real) • dir j = x := by
  simp

/-- A chart function carrying its first and second directional derivatives along
the coordinate directions, together with the witnesses relating them.  This is
the only smoothness requested anywhere in this file. -/
structure ChartJet (n : Nat) where
  /-- The function itself. -/
  val : (Fin n -> Real) -> Complex
  /-- Its first directional derivatives `d_j`. -/
  d : Fin n -> (Fin n -> Real) -> Complex
  /-- Its second directional derivatives `d2 j k = d_j (d_k)`. -/
  d2 : Fin n -> Fin n -> (Fin n -> Real) -> Complex
  /-- `d j` really is the derivative of `val` along `dir j`. -/
  hasDeriv : ∀ (j : Fin n) (x : Fin n -> Real),
    HasDerivAt (fun t : Real => val (x + t • dir j)) (d j x) 0
  /-- `d2 j k` really is the derivative of `d k` along `dir j`. -/
  hasDeriv2 : ∀ (j k : Fin n) (x : Fin n -> Real),
    HasDerivAt (fun t : Real => d k (x + t • dir j)) (d2 j k x) 0

namespace ChartJet

variable (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
  (B : Fin n -> (Fin n -> Real) -> Complex)

/-- A second-order operator with variable coefficients. -/
def waveOp (u : ChartJet n) (x : Fin n -> Real) : Complex :=
  (∑ j, ∑ k, A j k x * u.d2 j k x) + ∑ j, B j x * u.d j x

/-- The source's eikonal symbol `S phi = <d phi, d phi>_g`. -/
def eikonalSymbol (phi : ChartJet n) (x : Fin n -> Real) : Complex :=
  ∑ j, ∑ k, A j k x * phi.d j x * phi.d k x

/-- The source's transport expression `2 <d phi, d a>_g + (Box_g phi) a`. -/
def transportTerm (phi a : ChartJet n) (x : Fin n -> Real) : Complex :=
  (∑ j, ∑ k, A j k x * (a.d j x * phi.d k x + a.d k x * phi.d j x))
    + a.val x * waveOp A B phi x

/-! ## The beam and its derivative data -/

/-- The beam `a e^{w phi}`, with its first and second directional derivatives
constructed from those of `phi` and `a`. -/
def beam (w : Complex) (phi a : ChartJet n) : ChartJet n where
  val := fun x => a.val x * Complex.exp (w * phi.val x)
  d := fun j x => (a.d j x + w * a.val x * phi.d j x) * Complex.exp (w * phi.val x)
  d2 := fun j k x =>
    (a.d2 j k x
        + w * (a.d j x * phi.d k x + a.d k x * phi.d j x + a.val x * phi.d2 j k x)
        + w ^ 2 * a.val x * phi.d j x * phi.d k x)
      * Complex.exp (w * phi.val x)
  hasDeriv := by
    intro j x
    have hp := phi.hasDeriv j x
    have hE : HasDerivAt
        (fun t : Real => Complex.exp (w * phi.val (x + t • dir j)))
        (Complex.exp (w * phi.val x) * (w * phi.d j x)) 0 := by
      have h := (hp.const_mul w).cexp
      simpa using h
    have hprod := (a.hasDeriv j x).mul hE
    simp only [add_zero_smul_dir] at hprod
    convert hprod using 1
    ring
  hasDeriv2 := by
    intro j k x
    have hp := phi.hasDeriv j x
    have hE : HasDerivAt
        (fun t : Real => Complex.exp (w * phi.val (x + t • dir j)))
        (Complex.exp (w * phi.val x) * (w * phi.d j x)) 0 := by
      have h := (hp.const_mul w).cexp
      simpa using h
    have hinner : HasDerivAt
        (fun t : Real =>
          a.d k (x + t • dir j) + w * a.val (x + t • dir j) * phi.d k (x + t • dir j))
        (a.d2 j k x + (w * a.d j x * phi.d k x + w * a.val x * phi.d2 j k x)) 0 := by
      have h1 := a.hasDeriv2 j k x
      have h2 := ((a.hasDeriv j x).const_mul w).mul (phi.hasDeriv2 j k x)
      simp only [add_zero_smul_dir] at h2
      exact h1.add h2
    have hprod := hinner.mul hE
    simp only [add_zero_smul_dir] at hprod
    convert hprod using 1
    ring

@[simp] theorem beam_val (w : Complex) (phi a : ChartJet n) (x : Fin n -> Real) :
    (beam w phi a).val x = a.val x * Complex.exp (w * phi.val x) := rfl

@[simp] theorem beam_d (w : Complex) (phi a : ChartJet n) (j : Fin n)
    (x : Fin n -> Real) :
    (beam w phi a).d j x
      = (a.d j x + w * a.val x * phi.d j x) * Complex.exp (w * phi.val x) := rfl

@[simp] theorem beam_d2 (w : Complex) (phi a : ChartJet n) (j k : Fin n)
    (x : Fin n -> Real) :
    (beam w phi a).d2 j k x
      = (a.d2 j k x
          + w * (a.d j x * phi.d k x + a.d k x * phi.d j x + a.val x * phi.d2 j k x)
          + w ^ 2 * a.val x * phi.d j x * phi.d k x)
        * Complex.exp (w * phi.val x) := rfl

/-! ## The assembled WKB identity -/

/-- Pulling the exponential out of a doubly indexed coefficient sum. -/
theorem sum_mul_right (x : Fin n -> Real) (E : Complex)
    (f : Fin n -> Fin n -> Complex) :
    (∑ j, ∑ k, A j k x * (f j k * E)) = (∑ j, ∑ k, A j k x * f j k) * E := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Pulling the exponential out of a singly indexed coefficient sum. -/
theorem sum_mul_right' (x : Fin n -> Real) (E : Complex)
    (f : Fin n -> Complex) :
    (∑ j, B j x * (f j * E)) = (∑ j, B j x * f j) * E := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The assembled WKB identity.**  Applying the variable-coefficient
second-order operator to the beam `a e^{w phi}` produces exactly the source's
three-term expansion: the amplitude's own image, the transport expression at
first order in the frequency, and the eikonal symbol at second order. -/
theorem waveOp_beam (w : Complex) (phi a : ChartJet n) (x : Fin n -> Real) :
    waveOp A B (beam w phi a) x
      = Complex.exp (w * phi.val x)
        * (waveOp A B a x
            + w * transportTerm A B phi a x
            + w ^ 2 * a.val x * eikonalSymbol A phi x) := by
  have hA : (∑ j, ∑ k, A j k x
        * (a.d2 j k x
            + w * (a.d j x * phi.d k x + a.d k x * phi.d j x + a.val x * phi.d2 j k x)
            + w ^ 2 * a.val x * phi.d j x * phi.d k x))
      = (∑ j, ∑ k, A j k x * a.d2 j k x)
        + w * (∑ j, ∑ k, A j k x * (a.d j x * phi.d k x + a.d k x * phi.d j x))
        + w * (a.val x * ∑ j, ∑ k, A j k x * phi.d2 j k x)
        + w ^ 2 * (a.val x * ∑ j, ∑ k, A j k x * phi.d j x * phi.d k x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hB : (∑ j, B j x * (a.d j x + w * a.val x * phi.d j x))
      = (∑ j, B j x * a.d j x) + w * (a.val x * ∑ j, B j x * phi.d j x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [waveOp, transportTerm, eikonalSymbol, beam_d2, beam_d]
  rw [sum_mul_right A x (Complex.exp (w * phi.val x)) _,
    sum_mul_right' B x (Complex.exp (w * phi.val x)) _, hA, hB]
  ring

/-- **The source's displayed form.**  At the frequency `w = i rho` the identity
reads `rho^2` at second order and `i rho` at first, matching the displayed
expansion of Section 3.1 once the signature convention of the module docstring
is applied. -/
theorem waveOp_beam_freq (rho : Real) (phi a : ChartJet n) (x : Fin n -> Real) :
    waveOp A B (beam (Complex.I * (rho : Complex)) phi a) x
      = Complex.exp (Complex.I * (rho : Complex) * phi.val x)
        * (waveOp A B a x
            + Complex.I * (rho : Complex) * transportTerm A B phi a x
            - (rho : Complex) ^ 2 * a.val x * eikonalSymbol A phi x) := by
  rw [waveOp_beam A B]
  have hsq : (Complex.I * (rho : Complex)) ^ 2 = -((rho : Complex) ^ 2) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination ((rho : Complex) ^ 2) * hI
  rw [hsq]
  ring

end ChartJet

end LiuWang2025SemilinearWaveChartWKB
