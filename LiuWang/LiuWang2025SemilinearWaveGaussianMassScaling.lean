import LiuWang.LiuWang2025SemilinearWaveGaussianBoundaryScaling
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Liu--Wang 2025: the transverse Gaussian mass and the source exponent `d/4`

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Sections 3.1--3.2.

The source's beam estimates all rest on one scaling fact: a Gaussian beam of
frequency `rho` concentrated on a null geodesic occupies a transverse region of
width `rho^{-1/2}` in each of the `d` transverse directions, so its squared
`L^2` mass carries a factor `rho^{-d/2}` and its `L^2` norm the factor
`rho^{-d/4}` appearing in the paper's displayed exponent

`rho^{-((N - k + 1)/2 + d/4)}`.

`LiuWang2025SemilinearWaveGaussianBoundaryScaling` audits that exponent
symbolically.  This module computes the integral itself.

## Contents

* `integral_scaledGaussian` : `int_R e^{-(b rho) x^2} dx = sqrt(pi/b) / sqrt rho`
  for `b, rho > 0`, from Mathlib's Gaussian integral;
* `integral_scaledGaussian_pi` : the `d`-dimensional product form
  `int_{R^d} e^{-(b rho) |z|^2} dz = (sqrt(pi/b))^d (sqrt rho)^{-d}`;
* `integral_scaledGaussian_rpow` : the same written as
  `(pi/b)^{d/2} * rho^{-d/2}`, so the squared mass carries exactly `rho^{-d/2}`;
* `sqrt_integral_scaledGaussian` : taking the square root produces the source's
  `rho^{-d/4}`.

## Scope

This is the transverse mass of the *Gaussian profile*.  Bounding the beam
amplitude and its jets by such a profile, and integrating the resulting
estimate against the surface measure, are the surrounding source-specific
steps; the scaling factor itself is now computed rather than postulated.
-/

noncomputable section

open Real MeasureTheory
open scoped BigOperators

namespace LiuWang2025SemilinearWaveGaussianMassScaling

/-! ## The one-dimensional scaled Gaussian -/

/-- The frequency-scaled one-dimensional Gaussian integral. -/
theorem integral_scaledGaussian {b rho : Real} (hb : 0 < b) (hrho : 0 < rho) :
    (∫ x : Real, Real.exp (-(b * rho) * x ^ 2))
      = Real.sqrt (Real.pi / b) / Real.sqrt rho := by
  rw [integral_gaussian (b * rho)]
  rw [show Real.pi / (b * rho) = (Real.pi / b) * rho⁻¹ by field_simp]
  rw [Real.sqrt_mul (by positivity) _, Real.sqrt_inv]
  field_simp

/-- The scaled Gaussian is integrable. -/
theorem integrable_scaledGaussian {b rho : Real} (hb : 0 < b) (hrho : 0 < rho) :
    Integrable (fun x : Real => Real.exp (-(b * rho) * x ^ 2)) := by
  have hpos : 0 < b * rho := mul_pos hb hrho
  simpa using integrable_exp_neg_mul_sq hpos

/-! ## The `d`-dimensional transverse mass -/

/-- The squared transverse radius. -/
def radiusSq {d : Nat} (z : Fin d -> Real) : Real := ∑ i, (z i) ^ 2

/-- **The transverse Gaussian mass.**  Each of the `d` transverse directions
contributes one factor `(sqrt rho)^{-1}`. -/
theorem integral_scaledGaussian_pi {d : Nat} {b rho : Real}
    (hb : 0 < b) (hrho : 0 < rho) :
    (∫ z : Fin d -> Real, Real.exp (-(b * rho) * radiusSq z))
      = (Real.sqrt (Real.pi / b) / Real.sqrt rho) ^ d := by
  have hsplit : ∀ z : Fin d -> Real,
      Real.exp (-(b * rho) * radiusSq z)
        = ∏ i, Real.exp (-(b * rho) * (z i) ^ 2) := by
    intro z
    rw [radiusSq, ← Real.exp_sum, Finset.mul_sum]
  calc (∫ z : Fin d -> Real, Real.exp (-(b * rho) * radiusSq z))
      = ∫ z : Fin d -> Real, ∏ i, Real.exp (-(b * rho) * (z i) ^ 2) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z)
    _ = ∏ _i : Fin d, ∫ x : Real, Real.exp (-(b * rho) * x ^ 2) := by
        rw [MeasureTheory.volume_pi]
        exact integral_fintype_prod_eq_prod (fun _ x => Real.exp (-(b * rho) * x ^ 2))
    _ = (Real.sqrt (Real.pi / b) / Real.sqrt rho) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          integral_scaledGaussian hb hrho]

/-! ## The source exponents `d/2` and `d/4` -/

theorem sqrtInv_eq_rpow {rho : Real} (hrho : 0 < rho) :
    (Real.sqrt rho)⁻¹ = rho ^ (-(1 : Real) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hrho.le]
  norm_num

/-- **The squared transverse mass carries exactly `rho^{-d/2}`.** -/
theorem integral_scaledGaussian_rpow {d : Nat} {b rho : Real}
    (hb : 0 < b) (hrho : 0 < rho) :
    (∫ z : Fin d -> Real, Real.exp (-(b * rho) * radiusSq z))
      = Real.sqrt (Real.pi / b) ^ d * rho ^ (-(d : Real) / 2) := by
  rw [integral_scaledGaussian_pi hb hrho, div_pow, div_eq_mul_inv]
  congr 1
  rw [← inv_pow, sqrtInv_eq_rpow hrho,
    ← Real.rpow_natCast (rho ^ (-(1 : Real) / 2)) d, ← Real.rpow_mul hrho.le]
  congr 1
  ring

/-- **The `L^2` norm of the transverse Gaussian profile carries the source's
`rho^{-d/4}`.** -/
theorem sqrt_integral_scaledGaussian {d : Nat} {b rho : Real}
    (hb : 0 < b) (hrho : 0 < rho) :
    Real.sqrt (∫ z : Fin d -> Real, Real.exp (-(b * rho) * radiusSq z))
      = Real.sqrt (Real.sqrt (Real.pi / b) ^ d) * rho ^ (-(d : Real) / 4) := by
  rw [integral_scaledGaussian_rpow hb hrho, Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrho.le]
  congr 1
  ring

/-! ## Transverse moments: each `z` factor costs one half-power of `rho` -/

/-- Change of variables `x |-> (sqrt rho) x` on the line. -/
theorem integral_comp_sqrt_scaling (f : Real -> Real) {rho : Real} (_hrho : 0 < rho) :
    (∫ x : Real, f (Real.sqrt rho * x))
      = (Real.sqrt rho)⁻¹ * ∫ y : Real, f y := by
  have h := MeasureTheory.Measure.integral_comp_mul_left f (Real.sqrt rho)
  rw [h, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg rho)), smul_eq_mul]

/-- **The moment scaling identity.**  The `2m`-th moment of the
frequency-scaled Gaussian is `rho^{-(m + 1/2)}` times the unscaled moment, so
each transverse coordinate factor costs exactly one half-power of `rho`. -/
theorem integral_moment_scaledGaussian (m : Nat) {b rho : Real}
    (_hb : 0 < b) (hrho : 0 < rho) :
    rho ^ m * (∫ x : Real, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = (Real.sqrt rho)⁻¹ * ∫ y : Real, y ^ (2 * m) * Real.exp (-b * y ^ 2) := by
  have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt hrho.le
  have hscale := integral_comp_sqrt_scaling
    (fun y : Real => y ^ (2 * m) * Real.exp (-b * y ^ 2)) hrho
  have hrewrite : ∀ x : Real,
      (Real.sqrt rho * x) ^ (2 * m) * Real.exp (-b * (Real.sqrt rho * x) ^ 2)
        = rho ^ m * (x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2)) := by
    intro x
    have hpow : (Real.sqrt rho * x) ^ (2 * m) = rho ^ m * x ^ (2 * m) := by
      rw [mul_pow, pow_mul, hsq]
    have hexp : Real.exp (-b * (Real.sqrt rho * x) ^ 2)
        = Real.exp (-(b * rho) * x ^ 2) := by
      congr 1
      rw [mul_pow, hsq]
      ring
    rw [hpow, hexp]
    ring
  rw [← hscale]
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall hrewrite)]
  rw [MeasureTheory.integral_const_mul]

/-- The same in `rpow` form. -/
theorem integral_moment_scaledGaussian_rpow (m : Nat) {b rho : Real}
    (hb : 0 < b) (hrho : 0 < rho) :
    (∫ x : Real, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = rho ^ (-((m : Real) + 1 / 2))
        * ∫ y : Real, y ^ (2 * m) * Real.exp (-b * y ^ 2) := by
  have hkey := integral_moment_scaledGaussian m hb hrho
  have hrhom : (rho : Real) ^ m ≠ 0 := pow_ne_zero _ hrho.ne'
  have hsplit : rho ^ (-((m : Real) + 1 / 2))
      = (rho ^ m)⁻¹ * (Real.sqrt rho)⁻¹ := by
    rw [sqrtInv_eq_rpow hrho]
    rw [show -((m : Real) + 1 / 2) = (-(m : Real)) + (-(1 : Real) / 2) by ring]
    rw [Real.rpow_add hrho]
    congr 1
    rw [Real.rpow_neg hrho.le, Real.rpow_natCast]
  rw [hsplit, mul_assoc, ← hkey, ← mul_assoc, inv_mul_cancel₀ hrhom, one_mul]

/-- The `L^2` form of the moment scaling. -/
theorem sqrt_integral_moment_scaledGaussian (m : Nat) {b rho : Real}
    (hb : 0 < b) (hrho : 0 < rho) :
    Real.sqrt (∫ x : Real, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = rho ^ (-((m : Real) / 2 + 1 / 4))
        * Real.sqrt (∫ y : Real, y ^ (2 * m) * Real.exp (-b * y ^ 2)) := by
  rw [integral_moment_scaledGaussian_rpow m hb hrho,
    Real.sqrt_mul (Real.rpow_nonneg hrho.le _)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrho.le]
  congr 1
  ring

/-- **The source's transverse `L^2` rate.**  A beam profile carrying `k`
frequency powers and `m` transverse coordinate factors has `L^2` norm of order
`rho^{k - m/2 - 1/4}` in each transverse direction: the frequency powers count
positively, each transverse factor costs a half-power, and the Gaussian width
costs the quarter-power. -/
theorem beamProfile_L2_rate (k m : Nat) {b rho : Real}
    (hb : 0 < b) (hrho : 0 < rho) :
    rho ^ (k : Real)
        * Real.sqrt (∫ x : Real, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = rho ^ ((k : Real) - (m : Real) / 2 - 1 / 4)
        * Real.sqrt (∫ y : Real, y ^ (2 * m) * Real.exp (-b * y ^ 2)) := by
  rw [sqrt_integral_moment_scaledGaussian m hb hrho, ← mul_assoc,
    ← Real.rpow_add hrho]
  congr 2
  ring

/-- One reviewable object: the computed transverse Gaussian scaling behind the
source's displayed exponent. -/
structure Certificate (d : Nat) (b rho : Real) : Prop where
  oneDimensional : 0 < b -> 0 < rho ->
    (∫ x : Real, Real.exp (-(b * rho) * x ^ 2))
      = Real.sqrt (Real.pi / b) / Real.sqrt rho
  squaredMass : 0 < b -> 0 < rho ->
    (∫ z : Fin d -> Real, Real.exp (-(b * rho) * radiusSq z))
      = Real.sqrt (Real.pi / b) ^ d * rho ^ (-(d : Real) / 2)
  normScaling : 0 < b -> 0 < rho ->
    Real.sqrt (∫ z : Fin d -> Real, Real.exp (-(b * rho) * radiusSq z))
      = Real.sqrt (Real.sqrt (Real.pi / b) ^ d) * rho ^ (-(d : Real) / 4)
  momentScaling : 0 < b -> 0 < rho -> ∀ m : Nat,
    (∫ x : Real, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = rho ^ (-((m : Real) + 1 / 2))
        * ∫ y : Real, y ^ (2 * m) * Real.exp (-b * y ^ 2)
  transverseL2Rate : 0 < b -> 0 < rho -> ∀ k m : Nat,
    rho ^ (k : Real)
        * Real.sqrt (∫ x : Real, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = rho ^ ((k : Real) - (m : Real) / 2 - 1 / 4)
        * Real.sqrt (∫ y : Real, y ^ (2 * m) * Real.exp (-b * y ^ 2))

/-- The scaling certificate is computed, not assumed. -/
def certificate (d : Nat) (b rho : Real) : Certificate d b rho where
  oneDimensional := fun hb hrho => integral_scaledGaussian hb hrho
  squaredMass := fun hb hrho => integral_scaledGaussian_rpow hb hrho
  normScaling := fun hb hrho => sqrt_integral_scaledGaussian hb hrho
  momentScaling := fun hb hrho m => integral_moment_scaledGaussian_rpow m hb hrho
  transverseL2Rate := fun hb hrho k m => beamProfile_L2_rate k m hb hrho

/-- The computed norm exponent is the source's `d/4` term. -/
theorem normScaling_exponent_eq_sourceTerm (d : Nat) :
    -(d : Real) / 4 = -((d : Real) / 4) := by ring

end LiuWang2025SemilinearWaveGaussianMassScaling
