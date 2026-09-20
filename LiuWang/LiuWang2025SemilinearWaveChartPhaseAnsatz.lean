import LiuWang.LiuWang2025SemilinearWaveChartQuadraticPhase
import LiuWang.LiuWang2025SemilinearWaveTransverseJet

/-!
# Liu-Wang semilinear wave: the source's phase ansatz

Section 3 of the source writes the beam phase as

  `phi_0 = 0`,  `phi_1 = z^1`,  `phi_2 = z^T M(s) z`,

plus homogeneous terms of degree `3, ..., N`.  This file encodes the first three
of those as genuine `ChartJet`s -- value, first and second directional
derivative data, every derivative certified -- and records what the jet data
actually is:

* `phaseAnsatz2_val_zero`  : `phi(0) = 0`, the source's `phi_0 = 0`;
* `phaseAnsatz2_d_at_zero` : `d_{z^i} phi (0) = delta_{i,i0}`, the source's
  normalization of the linear term;
* `phaseAnsatz2_d2`        : the transverse 2-jet is `M_{ml} + M_{lm}`, the
  symmetrized Riccati unknown.

The degree-two eikonal cancellation itself is *not* restated here: it is
already proved, from actual derivatives of the Fermi metric components, in
`LiuWang2025SemilinearWaveFermiEikonalJet`
(`eikonal_secondJet_eq_zero_of_riccati` and its converse
`riccati_of_eikonal_secondJet_eq_zero`).  This file only supplies the phase
object that those theorems are about.

The homogeneous terms of degree `3, ..., N` are *not* constructed here.  The
triangular recursion producing them in variable geometry remains open, and the
dossier's stage list records that.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartPhaseAnsatz

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartQuadraticPhase

variable {n : Nat}

/-- Sum of two chart jets: the derivative data adds. -/
def ChartJet.add (u v : ChartJet n) : ChartJet n where
  val := fun x => u.val x + v.val x
  d := fun j x => u.d j x + v.d j x
  d2 := fun j k x => u.d2 j k x + v.d2 j k x
  hasDeriv := fun j x => (u.hasDeriv j x).add (v.hasDeriv j x)
  hasDeriv2 := fun j k x => (u.hasDeriv2 j k x).add (v.hasDeriv2 j k x)

@[simp] theorem ChartJet.add_val (u v : ChartJet n) (x : Fin n -> Real) :
    (ChartJet.add u v).val x = u.val x + v.val x := rfl

@[simp] theorem ChartJet.add_d (u v : ChartJet n) (j : Fin n) (x : Fin n -> Real) :
    (ChartJet.add u v).d j x = u.d j x + v.d j x := rfl

@[simp] theorem ChartJet.add_d2 (u v : ChartJet n) (j k : Fin n)
    (x : Fin n -> Real) :
    (ChartJet.add u v).d2 j k x = u.d2 j k x + v.d2 j k x := rfl

/-- **The source's linear phase term `phi_1 = z^1`**, as a constructed jet. -/
def linearJet (i0 : Fin n) : ChartJet n where
  val := fun x => ((x i0 : Real) : Complex)
  d := fun j _ => ((dir j i0 : Real) : Complex)
  d2 := fun _ _ _ => 0
  hasDeriv := by
    intro j x
    have hbase := hasDerivAt_lineC (x i0) (dir j i0)
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards with t
    show (((x + t • dir j) i0 : Real) : Complex)
      = ((x i0 : Real) : Complex) + ((t : Real) : Complex) * ((dir j i0 : Real) : Complex)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul]
  hasDeriv2 := by
    intro j k x
    exact hasDerivAt_const 0 _

@[simp] theorem linearJet_val (i0 : Fin n) (x : Fin n -> Real) :
    (linearJet i0).val x = ((x i0 : Real) : Complex) := rfl

/-- **The source's phase ansatz through second order**, `phi_1 + phi_2`. -/
def phaseAnsatz2 (i0 : Fin n) (M : Fin n -> Fin n -> Complex) : ChartJet n :=
  ChartJet.add (linearJet i0) (quadraticPhaseJet M 0)

/-- The source's `phi_0 = 0`: the ansatz vanishes on the central ray. -/
@[simp] theorem phaseAnsatz2_val_zero (i0 : Fin n) (M : Fin n -> Fin n -> Complex) :
    (phaseAnsatz2 i0 M).val 0 = 0 := by
  simp [phaseAnsatz2, quadVal]

/-- The source's normalization of the linear term: at the centre the phase
gradient is the `i0`-th covector. -/
theorem phaseAnsatz2_d_at_zero (i0 : Fin n) (M : Fin n -> Fin n -> Complex)
    (j : Fin n) :
    (phaseAnsatz2 i0 M).d j 0 = ((dir j i0 : Real) : Complex) := by
  show ((dir j i0 : Real) : Complex) + quadD M j 0 = _
  have hq : quadD M j (0 : Fin n -> Real) = 0 := by
    rw [quadD]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    simp
  rw [hq, add_zero]

/-- The transverse 2-jet of the ansatz is the symmetrized Riccati unknown. -/
theorem phaseAnsatz2_d2 (i0 : Fin n) (M : Fin n -> Fin n -> Complex)
    (l m : Fin n) (x : Fin n -> Real) :
    (phaseAnsatz2 i0 M).d2 l m x = M m l + M l m := by
  show (0 : Complex) + (quadraticPhaseJet M 0).d2 l m x = _
  rw [zero_add, quadraticPhaseJet_d2]

/-- The ansatz's imaginary part is coercive as soon as the imaginary quadratic
form is positive definite: the linear term is real and contributes nothing. -/
theorem phaseAnsatz2_im_coercive (i0 : Fin n) (M : Fin n -> Fin n -> Complex)
    {bcoer : Real}
    (hpos : ∀ x : Fin n -> Real,
      bcoer * LiuWang2025SemilinearWaveGaussianMassScaling.radiusSq x
        ≤ ∑ p, ∑ q, (M p q).im * x p * x q)
    (x : Fin n -> Real) :
    bcoer * LiuWang2025SemilinearWaveGaussianMassScaling.radiusSq x
      ≤ ((phaseAnsatz2 i0 M).val x).im := by
  show _ ≤ (((x i0 : Real) : Complex) + quadVal M 0 x).im
  rw [Complex.add_im, Complex.ofReal_im, zero_add, quadVal_im]
  have h := hpos x
  simp only [Complex.zero_im]
  linarith

end LiuWang2025SemilinearWaveChartPhaseAnsatz
