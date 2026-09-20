import LiuWang.LiuWang2025SemilinearWaveChartBeamResidual
import LiuWang.LiuWang2025SemilinearWaveGaussianL2Bridge

/-!
# Liu-Wang semilinear wave: the constructed beam's residual profile and rate

`LiuWang2025SemilinearWaveChartBeamResidual` shows that, once the eikonal
symbol, the leading transport expression and the hierarchy cancel, the operator
applied to the beam leaves exactly `rho^{-N} Box_g b_N` times the exponential.
This file turns that *constructed* residual into the polynomial-times-Gaussian
profile bound that `LiuWang2025SemilinearWaveGaussianL2Bridge` consumes, and
reads off the transverse `L^2` rate.

Nothing about the size of the residual is assumed.  The two inputs are named and
local, and are exactly the source's:

* the transverse coercivity of the phase, `b |z|^2 <= Im phi(z)`, which is what
  the Riccati layer produces (`LiuWang2025SemilinearWaveGaussianPhaseCoercivity`);
* a bound `|Box_g b_N(z)| <= A |z|^p` on the *terminal* amplitude jet, which is
  the explicit bounded-coefficient assumption on the constructed hierarchy.

Everything else -- the factor `rho^{-N}`, the Gaussian weight, the integrability,
and the rate -- is derived.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace LiuWang2025SemilinearWaveChartBeamProfile

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamResidual
open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)

variable {n : Nat}
variable (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
  (B : Fin n -> (Fin n -> Real) -> Complex)

/-- The modulus of the beam's exponential is the Gaussian weight determined by
the imaginary part of the phase. -/
theorem norm_beamExponential (rho : Real) (phi : ChartJet n) (x : Fin n -> Real) :
    ‖Complex.exp (Complex.I * (rho : Complex) * phi.val x)‖
      = Real.exp (-(rho * (phi.val x).im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **The constructed residual satisfies the source's profile bound.**  The
`rho^{-N}` comes from the telescoping, the Gaussian weight from the phase's
transverse coercivity, and the transverse weight from the terminal jet's
bound. -/
theorem residual_radiusProfileBound (rho : Real) (hrho : 0 < rho)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat)
    {coer amp : Real} {p : Nat}
    (heik : ∀ x, eikonalSymbol A phi x = 0)
    (htrans0 : ∀ x, transportTerm A B phi (b 0) x = 0)
    (hhier : ∀ m ∈ Finset.range N, ∀ x,
      Complex.I * transportTerm A B phi (b (m + 1)) x + waveOp A B (b m) x = 0)
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (hterm : ∀ x, ‖waveOp A B (b N) x‖ ≤ amp * (radius x) ^ p) :
    RadiusProfileBound
      (fun x => waveOp A B (beam (Complex.I * (rho : Complex)) phi
        (truncatedAmplitude rho b N)) x)
      (amp * (rho⁻¹) ^ N) p (coer * rho) := by
  have hrhoC : (rho : Complex) ≠ 0 := by
    exact_mod_cast hrho.ne'
  intro x
  simp only []
  rw [waveOp_beam_eq_terminal A B rho hrhoC phi b N x (heik x) (htrans0 x)
    (fun m hm => hhier m hm x), norm_mul, norm_mul,
    norm_beamExponential rho phi x]
  have hinv : ‖((rho : Complex))⁻¹ ^ N‖ = (rho⁻¹) ^ N := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hrho.le]
  rw [hinv]
  have hgauss : Real.exp (-(rho * (phi.val x).im))
      ≤ Real.exp (-(coer * rho) * radiusSq x) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_left (hIm x) hrho.le
    linarith
  have hinvnn : (0 : Real) ≤ (rho⁻¹) ^ N := pow_nonneg (inv_nonneg.2 hrho.le) N
  calc Real.exp (-(rho * (phi.val x).im))
          * ((rho⁻¹) ^ N * ‖waveOp A B (b N) x‖)
      ≤ Real.exp (-(coer * rho) * radiusSq x)
          * ((rho⁻¹) ^ N * (amp * (radius x) ^ p)) := by
        refine mul_le_mul hgauss ?_
          (mul_nonneg hinvnn (norm_nonneg _)) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hterm x) hinvnn
    _ = amp * (rho⁻¹) ^ N * (radius x) ^ p
          * Real.exp (-(coer * rho) * radiusSq x) := by ring

/-- **The Gaussian-beam remainder estimate, derived.**  The constructed
residual's transverse `L^2` norm is `O(rho^{-N} rho^{-(p/2 + n/4)})`: the
frequency gain `rho^{-N}` comes from the telescoping of the hierarchy, and the
Gaussian gain `rho^{-(p/2 + n/4)}` from the computed transverse mass.  The rate
is not postulated anywhere. -/
theorem residual_L2_rate (rho : Real) (hrho : 0 < rho)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat)
    {coer amp : Real} {p : Nat} (hamp : 0 ≤ amp) (hcoer : 0 < coer)
    (heik : ∀ x, eikonalSymbol A phi x = 0)
    (htrans0 : ∀ x, transportTerm A B phi (b 0) x = 0)
    (hhier : ∀ m ∈ Finset.range N, ∀ x,
      Complex.I * transportTerm A B phi (b (m + 1)) x + waveOp A B (b m) x = 0)
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (hterm : ∀ x, ‖waveOp A B (b N) x‖ ≤ amp * (radius x) ^ p) :
    Real.sqrt (∫ x : Fin n -> Real,
        ‖waveOp A B (beam (Complex.I * (rho : Complex)) phi
          (truncatedAmplitude rho b N)) x‖ ^ 2)
      ≤ (amp * (rho⁻¹) ^ N)
          * rho ^ (-((p : Real) / 2 + (n : Real) / 4))
          * Real.sqrt (gaussianMoment n p (2 * coer)) := by
  refine sqrt_integral_normSq_le_of_radiusProfileBound
    (mul_nonneg hamp (pow_nonneg (inv_nonneg.2 hrho.le) N)) hcoer hrho ?_
  exact residual_radiusProfileBound A B rho hrho phi b N heik htrans0 hhier
    hIm hterm

end LiuWang2025SemilinearWaveChartBeamProfile
