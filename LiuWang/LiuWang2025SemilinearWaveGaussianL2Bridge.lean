import LiuWang.LiuWang2025SemilinearWaveGaussianMassScaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Liu-Wang semilinear wave: from a pointwise Gaussian profile to an `L^2` rate

`LiuWang2025SemilinearWaveGaussianMassScaling` computes the *mass* of the
frequency-scaled transverse Gaussian, one transverse line at a time.  What the
source actually uses, both in the Gaussian-beam remainder estimate and in the
estimate on the inaccessible part of the lateral boundary, is the implication

> a pointwise bound `|f(z)| <= C |z|^{2m} e^{-w |z|^2}` on the transverse slice
> forces `|| f ||_{L^2} <= C * (moment)^{1/2} * rho^{-(m + d/4)}`.

That implication is the missing analytic step: the scaling identity alone says
nothing about a function which merely *satisfies* the profile bound.  This file
supplies it, in the `d`-dimensional transverse variable, with

* `pow_le_const_mul_exp` and `moment_le_gaussian`, the elementary majorant
  `s^m e^{-c s} <= (2m/c)^m e^{-(c/2) s}` valid for `s >= 0`;
* `integrable_gaussian_pi` and `integrable_moment_pi`, integrability of the
  transverse Gaussian and of every polynomial multiple of it on `Fin d -> Real`;
* `integral_moment_scaledGaussian_pi`, the `d`-dimensional moment scaling
  `int |z|^{2m} e^{-(b rho)|z|^2} = rho^{-(m + d/2)} * int |y|^{2m} e^{-b|y|^2}`,
  obtained from the additive Haar dilation `z |-> sqrt(rho) z`;
* `integral_normSq_le_of_profileBound` and
  `sqrt_integral_normSq_le_of_profileBound`, the bridge itself;
* `profileBound_of_beam` and `beamProfile_L2_rate_of_beam`, the instantiation at
  an actual Gaussian beam `e^{i rho phi} a` whose phase satisfies the source's
  coercivity `Im phi >= b |z|^2` and whose amplitude is dominated by `A |z|^{2m}`.

The exponent produced, `rho^{-(m + d/4)}`, is exactly the transverse part of the
source's displayed boundary decay rate: `d/4` from the Gaussian width and one
half-power for each transverse coordinate factor carried by the amplitude jet.

Nothing here is assumed: the majorant, its integrability, the dilation identity
and the resulting `L^2` bound are all proved.  The geometric inputs that remain
source-specific -- that the reflected beam's phase really has the coercivity
`Im phi >= b |z|^2` in Fermi coordinates, and that the amplitude jets really are
dominated by `A |z|^{2m}` near the reflection point -- enter as *hypotheses* of
the theorems below, to be supplied by the reflected-beam construction.
-/

noncomputable section

open Real MeasureTheory
open scoped BigOperators

namespace LiuWang2025SemilinearWaveGaussianL2Bridge

open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)

/-! ## The transverse radius -/

/-- The transverse radius squared is nonnegative. -/
theorem radiusSq_nonneg {d : Nat} (z : Fin d -> Real) : 0 ≤ radiusSq z := by
  show (0 : Real) ≤ ∑ i, (z i) ^ 2
  exact Finset.sum_nonneg fun i _ => sq_nonneg (z i)

/-- The transverse radius squared is continuous. -/
theorem continuous_radiusSq {d : Nat} :
    Continuous (radiusSq : (Fin d -> Real) -> Real) := by
  show Continuous fun z : Fin d -> Real => ∑ i, (z i) ^ 2
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2

/-- The dilation `z |-> r z` scales the transverse radius by `r^2`. -/
theorem radiusSq_smul {d : Nat} (r : Real) (z : Fin d -> Real) :
    radiusSq (r • z) = r ^ 2 * radiusSq z := by
  rw [radiusSq, radiusSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_pow]

/-! ## Comparison with the ambient norm

`Fin d -> Real` carries the supremum norm, while the transverse Gaussian is
written with the Euclidean radius.  The two are equivalent, and the comparison
below is what lets a profile bound stated in the ambient norm -- as the
summed-phase and stationary-phase layers state theirs -- be fed to the bridge.
-/

/-- The supremum norm is dominated by the Euclidean radius. -/
theorem norm_sq_le_radiusSq {d : Nat} (z : Fin d -> Real) :
    ‖z‖ ^ 2 ≤ radiusSq z := by
  have hnn : (0 : Real) ≤ Real.sqrt (radiusSq z) := Real.sqrt_nonneg _
  have hle : ‖z‖ ≤ Real.sqrt (radiusSq z) := by
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
    have hsingle : (z i) ^ 2 ≤ radiusSq z := by
      rw [radiusSq]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsingle
  calc ‖z‖ ^ 2 ≤ Real.sqrt (radiusSq z) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg z) hle 2
    _ = radiusSq z := Real.sq_sqrt (radiusSq_nonneg z)

/-- The Euclidean radius is dominated by `d` times the supremum norm squared. -/
theorem radiusSq_le_dim_mul_norm_sq {d : Nat} (z : Fin d -> Real) :
    radiusSq z ≤ (d : Real) * ‖z‖ ^ 2 := by
  have hterm : ∀ i : Fin d, (z i) ^ 2 ≤ ‖z‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at h
    calc (z i) ^ 2 = |z i| ^ 2 := (sq_abs _).symm
      _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  calc radiusSq z = ∑ i, (z i) ^ 2 := rfl
    _ ≤ ∑ _i : Fin d, ‖z‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : Real) * ‖z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The elementary polynomial-times-Gaussian majorant -/

/-- `s^m <= (m/a)^m e^{a s}` for `s >= 0` and `a > 0`.  This is the only place
where the polynomial weight is traded for a fraction of the Gaussian. -/
theorem pow_le_const_mul_exp (m : Nat) {a : Real} (ha : 0 < a) {s : Real}
    (hs : 0 ≤ s) :
    s ^ m ≤ ((m : Real) / a) ^ m * Real.exp (a * s) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, one_mul]
    have h := Real.add_one_le_exp (a * s)
    have hnn : (0 : Real) ≤ a * s := mul_nonneg ha.le hs
    linarith
  · have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
    have hmne : (m : Real) ≠ 0 := ne_of_gt hmR
    have hane : a ≠ 0 := ne_of_gt ha
    have ht0 : (0 : Real) ≤ a * s / (m : Real) :=
      div_nonneg (mul_nonneg ha.le hs) hmR.le
    have ht : a * s / (m : Real) ≤ Real.exp (a * s / (m : Real)) := by
      have h := Real.add_one_le_exp (a * s / (m : Real))
      linarith
    have hpow : (a * s / (m : Real)) ^ m ≤ (Real.exp (a * s / (m : Real))) ^ m :=
      pow_le_pow_left₀ ht0 ht m
    have hexp : (Real.exp (a * s / (m : Real))) ^ m = Real.exp (a * s) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have hkey : ((m : Real) / a) ^ m * (a * s / (m : Real)) ^ m = s ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc s ^ m = ((m : Real) / a) ^ m * (a * s / (m : Real)) ^ m := hkey.symm
      _ ≤ ((m : Real) / a) ^ m * Real.exp (a * s) := by
          refine mul_le_mul_of_nonneg_left ?_
            (pow_nonneg (div_nonneg (Nat.cast_nonneg m) ha.le) m)
          exact hexp ▸ hpow

/-- The polynomial-times-Gaussian majorant: `s^m e^{-c s} <= (2m/c)^m e^{-(c/2)s}`
for `s >= 0`. -/
theorem moment_le_gaussian (m : Nat) {c s : Real} (hc : 0 < c) (hs : 0 ≤ s) :
    s ^ m * Real.exp (-c * s)
      ≤ (2 * (m : Real) / c) ^ m * Real.exp (-(c / 2) * s) := by
  have hc2 : (0 : Real) < c / 2 := by linarith
  have h := pow_le_const_mul_exp m hc2 hs
  have hconst : ((m : Real) / (c / 2)) = 2 * (m : Real) / c := by
    field_simp
  rw [hconst] at h
  calc s ^ m * Real.exp (-c * s)
      ≤ (2 * (m : Real) / c) ^ m * Real.exp (c / 2 * s) * Real.exp (-c * s) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (2 * (m : Real) / c) ^ m * Real.exp (-(c / 2) * s) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-! ## Integrability of the transverse majorants -/

/-- The transverse Gaussian is integrable on `Fin d -> Real`. -/
theorem integrable_gaussian_pi {d : Nat} {c : Real} (hc : 0 < c) :
    Integrable (fun z : Fin d -> Real => Real.exp (-c * radiusSq z)) := by
  have hsplit : (fun z : Fin d -> Real => Real.exp (-c * radiusSq z))
      = fun z : Fin d -> Real => ∏ i, Real.exp (-c * (z i) ^ 2) := by
    funext z
    rw [radiusSq, ← Real.exp_sum, Finset.mul_sum]
  rw [hsplit, MeasureTheory.volume_pi]
  exact MeasureTheory.Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq hc

/-- Every polynomial multiple of the transverse Gaussian is integrable. -/
theorem integrable_moment_pi {d : Nat} (m : Nat) {c : Real} (hc : 0 < c) :
    Integrable
      (fun z : Fin d -> Real => (radiusSq z) ^ m * Real.exp (-c * radiusSq z)) := by
  have hc2 : (0 : Real) < c / 2 := by linarith
  have hg : Integrable (fun z : Fin d -> Real =>
      (2 * (m : Real) / c) ^ m * Real.exp (-(c / 2) * radiusSq z)) :=
    (integrable_gaussian_pi (d := d) hc2).const_mul _
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((continuous_radiusSq.pow m).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_radiusSq))).aestronglyMeasurable
  · have hnorm : ‖(radiusSq z) ^ m * Real.exp (-c * radiusSq z)‖
        = (radiusSq z) ^ m * Real.exp (-c * radiusSq z) :=
      Real.norm_of_nonneg
        (mul_nonneg (pow_nonneg (radiusSq_nonneg z) m) (Real.exp_pos _).le)
    rw [hnorm]
    exact moment_le_gaussian m hc (radiusSq_nonneg z)

/-! ## The `d`-dimensional moment scaling -/

/-- The additive Haar dilation on `Fin d -> Real`. -/
theorem integral_comp_smul_pi {d : Nat} (G : (Fin d -> Real) -> Real) {r : Real}
    (hr : 0 ≤ r) :
    (∫ z : Fin d -> Real, G (r • z)) = (r ^ d)⁻¹ * ∫ y : Fin d -> Real, G y := by
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (Fin d -> Real))) G r (hR := hr)
  rw [h, Module.finrank_fin_fun, smul_eq_mul]

/-- The unscaled transverse moment of order `2m`. -/
def gaussianMoment (d m : Nat) (b : Real) : Real :=
  ∫ y : Fin d -> Real, (radiusSq y) ^ m * Real.exp (-b * radiusSq y)

/-- Transverse moments are nonnegative. -/
theorem gaussianMoment_nonneg (d m : Nat) (b : Real) : 0 ≤ gaussianMoment d m b :=
  integral_nonneg fun y =>
    mul_nonneg (pow_nonneg (radiusSq_nonneg y) m) (Real.exp_pos _).le

/-- The zeroth transverse moment is the computed Gaussian mass. -/
theorem gaussianMoment_zero (d : Nat) {b : Real} (hb : 0 < b) :
    gaussianMoment d 0 b = Real.sqrt (Real.pi / b) ^ d := by
  have h := LiuWang2025SemilinearWaveGaussianMassScaling.integral_scaledGaussian_pi
    (d := d) (b := b) (rho := 1) hb one_pos
  have hcongr : (∫ y : Fin d -> Real, Real.exp (-b * radiusSq y))
      = ∫ y : Fin d -> Real, Real.exp (-(b * 1) * radiusSq y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have harg : -b * radiusSq y = -(b * 1) * radiusSq y := by ring
    show Real.exp (-b * radiusSq y) = Real.exp (-(b * 1) * radiusSq y)
    rw [harg]
  rw [gaussianMoment]
  simp only [pow_zero, one_mul]
  rw [hcongr, h, Real.sqrt_one, div_one]

/-- The zeroth transverse moment is strictly positive: the `L^2` rates below are
not vacuous. -/
theorem gaussianMoment_zero_pos (d : Nat) {b : Real} (hb : 0 < b) :
    0 < gaussianMoment d 0 b := by
  rw [gaussianMoment_zero d hb]
  exact pow_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos hb)) d

/-- **The `d`-dimensional moment scaling.**  Each transverse coordinate factor
costs one half-power of `rho`, and the Gaussian width costs `rho^{-d/2}`. -/
theorem integral_moment_scaledGaussian_pi {d : Nat} (m : Nat) {b rho : Real}
    (_hb : 0 < b) (hrho : 0 < rho) :
    (∫ z : Fin d -> Real, (radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z))
      = rho ^ (-((m : Real) + (d : Real) / 2)) * gaussianMoment d m b := by
  have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt hrho.le
  have hscale := integral_comp_smul_pi
    (fun y : Fin d -> Real => (radiusSq y) ^ m * Real.exp (-b * radiusSq y))
    (Real.sqrt_nonneg rho)
  simp only at hscale
  have hrw : ∀ z : Fin d -> Real,
      (radiusSq (Real.sqrt rho • z)) ^ m * Real.exp (-b * radiusSq (Real.sqrt rho • z))
        = rho ^ m * ((radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z)) := by
    intro z
    have hexp : Real.exp (-b * (rho * radiusSq z))
        = Real.exp (-(b * rho) * radiusSq z) := by
      congr 1
      ring
    rw [radiusSq_smul, hsq, mul_pow, hexp, mul_assoc]
  have hL : (∫ z : Fin d -> Real,
        (radiusSq (Real.sqrt rho • z)) ^ m * Real.exp (-b * radiusSq (Real.sqrt rho • z)))
      = rho ^ m
        * ∫ z : Fin d -> Real, (radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrw),
      MeasureTheory.integral_const_mul]
  rw [hL] at hscale
  have hmoment : (∫ y : Fin d -> Real, (radiusSq y) ^ m * Real.exp (-b * radiusSq y))
      = gaussianMoment d m b := rfl
  rw [hmoment] at hscale
  have hsqrtpow : (Real.sqrt rho ^ d)⁻¹ = rho ^ (-(d : Real) / 2) := by
    rw [← inv_pow, LiuWang2025SemilinearWaveGaussianMassScaling.sqrtInv_eq_rpow hrho,
      ← Real.rpow_natCast (rho ^ (-(1 : Real) / 2)) d, ← Real.rpow_mul hrho.le]
    congr 1
    ring
  have hsplit : rho ^ (-((m : Real) + (d : Real) / 2))
      = (rho ^ m)⁻¹ * rho ^ (-(d : Real) / 2) := by
    rw [show -((m : Real) + (d : Real) / 2) = (-(m : Real)) + (-(d : Real) / 2) by ring,
      Real.rpow_add hrho, Real.rpow_neg hrho.le, Real.rpow_natCast]
  have hrhom : (rho : Real) ^ m ≠ 0 := pow_ne_zero _ hrho.ne'
  rw [hsplit, mul_assoc, ← hsqrtpow, ← hscale, ← mul_assoc, inv_mul_cancel₀ hrhom,
    one_mul]

/-! ## The bridge: a pointwise profile bound forces an `L^2` rate -/

/-- The source's pointwise transverse profile bound: `|f(z)| <= C |z|^{2m} e^{-w|z|^2}`. -/
def GaussianProfileBound {d : Nat} (f : (Fin d -> Real) -> Complex) (C : Real)
    (m : Nat) (w : Real) : Prop :=
  ∀ z, ‖f z‖ ≤ C * (radiusSq z) ^ m * Real.exp (-w * radiusSq z)

/-- Squaring the profile bound doubles both the weight and the Gaussian rate. -/
theorem normSq_le_of_profileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {w : Real} (hf : GaussianProfileBound f C m w)
    (z : Fin d -> Real) :
    ‖f z‖ ^ 2
      ≤ C ^ 2 * ((radiusSq z) ^ (2 * m) * Real.exp (-(2 * w) * radiusSq z)) := by
  have hexp2 : (Real.exp (-w * radiusSq z)) ^ 2
      = Real.exp (-(2 * w) * radiusSq z) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpow2 : ((radiusSq z) ^ m) ^ 2 = (radiusSq z) ^ (2 * m) := by
    rw [← pow_mul]
    congr 1
    ring
  calc ‖f z‖ ^ 2
      ≤ (C * (radiusSq z) ^ m * Real.exp (-w * radiusSq z)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hf z) 2
    _ = C ^ 2 * ((radiusSq z) ^ (2 * m) * Real.exp (-(2 * w) * radiusSq z)) := by
        rw [mul_pow, mul_pow, hpow2, hexp2, mul_assoc]

/-- **The bridge, squared form.**  A pointwise Gaussian profile bound with
frequency-scaled width `b rho` forces the transverse `L^2` square to obey the
computed scaling `rho^{-(2m + d/2)}`. -/
theorem integral_normSq_le_of_profileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {b rho : Real} (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f C m (b * rho)) :
    (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ C ^ 2 * (rho ^ (-(((2 * m : Nat) : Real) + (d : Real) / 2))
          * gaussianMoment d (2 * m) (2 * b)) := by
  have hbound2 : ∀ z : Fin d -> Real, ‖f z‖ ^ 2
      ≤ C ^ 2 * ((radiusSq z) ^ (2 * m) * Real.exp (-(2 * b * rho) * radiusSq z)) := by
    intro z
    have h := normSq_le_of_profileBound hf z
    rw [show (2 : Real) * (b * rho) = 2 * b * rho from by ring] at h
    exact h
  have hbrho : (0 : Real) < 2 * b * rho := by positivity
  have hmaj : Integrable (fun z : Fin d -> Real =>
      C ^ 2 * ((radiusSq z) ^ (2 * m) * Real.exp (-(2 * b * rho) * radiusSq z))) :=
    (integrable_moment_pi (d := d) (2 * m) hbrho).const_mul _
  calc (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ ∫ z : Fin d -> Real,
          C ^ 2 * ((radiusSq z) ^ (2 * m) * Real.exp (-(2 * b * rho) * radiusSq z)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => sq_nonneg _) hmaj
          (Filter.Eventually.of_forall hbound2)
    _ = C ^ 2 * ∫ z : Fin d -> Real,
          (radiusSq z) ^ (2 * m) * Real.exp (-(2 * b * rho) * radiusSq z) :=
        MeasureTheory.integral_const_mul _ _
    _ = C ^ 2 * (rho ^ (-(((2 * m : Nat) : Real) + (d : Real) / 2))
          * gaussianMoment d (2 * m) (2 * b)) := by
        rw [integral_moment_scaledGaussian_pi (d := d) (2 * m) (b := 2 * b) (by linarith) hrho]

/-- **The bridge, `L^2` form.**  The transverse `L^2` norm of a profile-bounded
function is `O(rho^{-(m + d/4)})`: one half-power of `rho` for each transverse
coordinate factor, and the source's `d/4` from the Gaussian width. -/
theorem sqrt_integral_normSq_le_of_profileBound {d : Nat}
    {f : (Fin d -> Real) -> Complex} {C : Real} {m : Nat} {b rho : Real}
    (hC : 0 ≤ C) (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f C m (b * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ C * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) := by
  have h := integral_normSq_le_of_profileBound hb hrho hf
  have hsqrtrpow : Real.sqrt (rho ^ (-(((2 * m : Nat) : Real) + (d : Real) / 2)))
      = rho ^ (-((m : Real) + (d : Real) / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrho.le]
    congr 1
    push_cast
    ring
  calc Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ Real.sqrt (C ^ 2 * (rho ^ (-(((2 * m : Nat) : Real) + (d : Real) / 2))
          * gaussianMoment d (2 * m) (2 * b))) := Real.sqrt_le_sqrt h
    _ = C * (rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * b))) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC,
          Real.sqrt_mul (Real.rpow_nonneg hrho.le _), hsqrtrpow]
    _ = C * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) := (mul_assoc _ _ _).symm

/-- The same with the frequency powers carried by the amplitude displayed
separately: a profile with `rho^k` in front has transverse `L^2` norm of order
`rho^{k - m - d/4}`. -/
theorem beamProfile_L2_rate {d : Nat} {f : (Fin d -> Real) -> Complex}
    {A k : Real} {m : Nat} {b rho : Real} (hA : 0 ≤ A) (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f (A * rho ^ k) m (b * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ A * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
          * rho ^ (k - (m : Real) - (d : Real) / 4) := by
  have hC : (0 : Real) ≤ A * rho ^ k := mul_nonneg hA (Real.rpow_nonneg hrho.le _)
  have h := sqrt_integral_normSq_le_of_profileBound hC hb hrho hf
  have hcomb : rho ^ k * rho ^ (-((m : Real) + (d : Real) / 4))
      = rho ^ (k - (m : Real) - (d : Real) / 4) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  refine h.trans_eq ?_
  calc A * rho ^ k * rho ^ (-((m : Real) + (d : Real) / 4))
        * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
      = A * (rho ^ k * rho ^ (-((m : Real) + (d : Real) / 4)))
        * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) := by ring
    _ = A * rho ^ (k - (m : Real) - (d : Real) / 4)
        * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) := by rw [hcomb]
    _ = A * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
        * rho ^ (k - (m : Real) - (d : Real) / 4) := by ring

/-! ## Arbitrary transverse weights `|z|^p`

The source's reflected-beam estimate carries the weight `|y|^{N+1-j+k}`, whose
parity is not fixed, so the even weight `|z|^{2m}` of the previous section does
not express it directly.  Squaring a `|z|^p` bound, however, produces the
*natural* power `(|z|^2)^p`, so the same moment scaling applies verbatim.
-/

/-- The transverse radius. -/
def radius {d : Nat} (z : Fin d -> Real) : Real := Real.sqrt (radiusSq z)

theorem radius_nonneg {d : Nat} (z : Fin d -> Real) : 0 ≤ radius z :=
  Real.sqrt_nonneg _

theorem radius_sq {d : Nat} (z : Fin d -> Real) : (radius z) ^ 2 = radiusSq z :=
  Real.sq_sqrt (radiusSq_nonneg z)

theorem radius_pow_sq {d : Nat} (p : Nat) (z : Fin d -> Real) :
    ((radius z) ^ p) ^ 2 = (radiusSq z) ^ p := by
  rw [← pow_mul, mul_comm p 2, pow_mul, radius_sq]

/-- The source's pointwise profile bound with an arbitrary transverse weight
`|z|^p`, `p` of either parity. -/
def RadiusProfileBound {d : Nat} (f : (Fin d -> Real) -> Complex) (C : Real)
    (p : Nat) (w : Real) : Prop :=
  ∀ z, ‖f z‖ ≤ C * (radius z) ^ p * Real.exp (-w * radiusSq z)

/-- Squaring a `|z|^p` bound gives the natural power `(|z|^2)^p`. -/
theorem normSq_le_of_radiusProfileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {p : Nat} {w : Real} (hf : RadiusProfileBound f C p w)
    (z : Fin d -> Real) :
    ‖f z‖ ^ 2 ≤ C ^ 2 * ((radiusSq z) ^ p * Real.exp (-(2 * w) * radiusSq z)) := by
  have hexp2 : (Real.exp (-w * radiusSq z)) ^ 2
      = Real.exp (-(2 * w) * radiusSq z) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc ‖f z‖ ^ 2
      ≤ (C * (radius z) ^ p * Real.exp (-w * radiusSq z)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hf z) 2
    _ = C ^ 2 * ((radiusSq z) ^ p * Real.exp (-(2 * w) * radiusSq z)) := by
        rw [mul_pow, mul_pow, radius_pow_sq, hexp2, mul_assoc]

/-- **The `L^2` rate for an arbitrary transverse weight.**  One half-power of
the frequency per unit of transverse weight, plus the Gaussian `d/4`. -/
theorem sqrt_integral_normSq_le_of_radiusProfileBound {d : Nat}
    {f : (Fin d -> Real) -> Complex} {C : Real} {p : Nat} {b rho : Real}
    (hC : 0 ≤ C) (hb : 0 < b) (hrho : 0 < rho)
    (hf : RadiusProfileBound f C p (b * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ C * rho ^ (-((p : Real) / 2 + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d p (2 * b)) := by
  have hbrho : (0 : Real) < 2 * b * rho := by positivity
  have hbound : ∀ z : Fin d -> Real, ‖f z‖ ^ 2
      ≤ C ^ 2 * ((radiusSq z) ^ p * Real.exp (-(2 * b * rho) * radiusSq z)) := by
    intro z
    have h := normSq_le_of_radiusProfileBound hf z
    rw [show (2 : Real) * (b * rho) = 2 * b * rho from by ring] at h
    exact h
  have hmaj : Integrable (fun z : Fin d -> Real =>
      C ^ 2 * ((radiusSq z) ^ p * Real.exp (-(2 * b * rho) * radiusSq z))) :=
    (integrable_moment_pi (d := d) p hbrho).const_mul _
  have hsq : (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ C ^ 2 * (rho ^ (-((p : Real) + (d : Real) / 2))
          * gaussianMoment d p (2 * b)) := by
    calc (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
        ≤ ∫ z : Fin d -> Real,
            C ^ 2 * ((radiusSq z) ^ p * Real.exp (-(2 * b * rho) * radiusSq z)) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => sq_nonneg _) hmaj
            (Filter.Eventually.of_forall hbound)
      _ = C ^ 2 * ∫ z : Fin d -> Real,
            (radiusSq z) ^ p * Real.exp (-(2 * b * rho) * radiusSq z) :=
          MeasureTheory.integral_const_mul _ _
      _ = C ^ 2 * (rho ^ (-((p : Real) + (d : Real) / 2))
            * gaussianMoment d p (2 * b)) := by
          rw [integral_moment_scaledGaussian_pi (d := d) p (b := 2 * b)
            (by linarith) hrho]
  have hsqrtrpow : Real.sqrt (rho ^ (-((p : Real) + (d : Real) / 2)))
      = rho ^ (-((p : Real) / 2 + (d : Real) / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrho.le]
    congr 1
    ring
  calc Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ Real.sqrt (C ^ 2 * (rho ^ (-((p : Real) + (d : Real) / 2))
          * gaussianMoment d p (2 * b))) := Real.sqrt_le_sqrt hsq
    _ = C * (rho ^ (-((p : Real) / 2 + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d p (2 * b))) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC,
          Real.sqrt_mul (Real.rpow_nonneg hrho.le _), hsqrtrpow]
    _ = C * rho ^ (-((p : Real) / 2 + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d p (2 * b)) := (mul_assoc _ _ _).symm

/-! ## The source's reflected-boundary estimate

Subsection 3.2 of the source bounds the tangential derivatives of the reflected
Gaussian beam on the reflecting face `R_1` by

`|d_y^alpha v_rho| <= C sum_{k+j=|alpha|} rho^k |y|^k e^{-C' rho |y|^2} |y|^{N+1-j}`,

performs the change of variables `y |-> rho^{-1/2} y`, and concludes

`|| v_rho ||_{H^k(R_1)} <= C rho^{-(N-k+1)/2 - 3/4}`.

The theorems below carry out exactly that computation, in general transverse
dimension: each term of the displayed sum has transverse `L^2` norm
`O(rho^{-(N-|alpha|+1)/2 - d/4})`, uniformly in the splitting `k+j=|alpha|`, and
so does the sum.  The source's displayed `3/4` is the Gaussian `d/4` at `d = 3`.
-/

/-- **One term of the source's reflected-boundary sum.**  A term carrying `k`
frequency powers and the transverse weight `|y|^{k + (N+1-j)}`, with
`k + j = |alpha|`, has transverse `L^2` norm `O(rho^{-(N-|alpha|+1)/2 - d/4})`.
The frequency powers and the weight combine so that only `|alpha|` survives. -/
theorem reflectedBoundaryTerm_L2_rate {d : Nat} {f : (Fin d -> Real) -> Complex}
    {A b rho : Real} {N alpha k j : Nat}
    (hkj : k + j = alpha) (hjN : j ≤ N + 1)
    (hA : 0 ≤ A) (hb : 0 < b) (hrho : 0 < rho)
    (hf : RadiusProfileBound f (A * rho ^ (k : Real)) (k + (N + 1 - j)) (b * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
      ≤ A * Real.sqrt (gaussianMoment d (k + (N + 1 - j)) (2 * b))
          * rho ^ (-(((N : Real) - (alpha : Real) + 1) / 2) - (d : Real) / 4) := by
  have hC : (0 : Real) ≤ A * rho ^ (k : Real) :=
    mul_nonneg hA (Real.rpow_nonneg hrho.le _)
  have h := sqrt_integral_normSq_le_of_radiusProfileBound hC hb hrho hf
  have hcast : ((k + (N + 1 - j) : Nat) : Real)
      = (k : Real) + ((N : Real) + 1 - (j : Real)) := by
    rw [Nat.cast_add, Nat.cast_sub hjN]
    push_cast
    ring
  have halpha : (alpha : Real) = (k : Real) + (j : Real) := by exact_mod_cast hkj.symm
  have hcomb : rho ^ (k : Real)
        * rho ^ (-(((k + (N + 1 - j) : Nat) : Real) / 2 + (d : Real) / 4))
      = rho ^ (-(((N : Real) - (alpha : Real) + 1) / 2) - (d : Real) / 4) := by
    rw [← Real.rpow_add hrho]
    congr 1
    rw [hcast, halpha]
    ring
  refine h.trans_eq ?_
  calc A * rho ^ (k : Real)
        * rho ^ (-(((k + (N + 1 - j) : Nat) : Real) / 2 + (d : Real) / 4))
        * Real.sqrt (gaussianMoment d (k + (N + 1 - j)) (2 * b))
      = A * (rho ^ (k : Real)
          * rho ^ (-(((k + (N + 1 - j) : Nat) : Real) / 2 + (d : Real) / 4)))
        * Real.sqrt (gaussianMoment d (k + (N + 1 - j)) (2 * b)) := by ring
    _ = A * rho ^ (-(((N : Real) - (alpha : Real) + 1) / 2) - (d : Real) / 4)
        * Real.sqrt (gaussianMoment d (k + (N + 1 - j)) (2 * b)) := by rw [hcomb]
    _ = A * Real.sqrt (gaussianMoment d (k + (N + 1 - j)) (2 * b))
        * rho ^ (-(((N : Real) - (alpha : Real) + 1) / 2) - (d : Real) / 4) := by ring

/-- **The source's reflected-boundary sum.**  Summing the displayed splitting
`k + j = |alpha|` leaves the exponent unchanged: the whole tangential derivative
obeys `O(rho^{-(N-|alpha|+1)/2 - d/4})`. -/
theorem reflectedBoundary_summed_L2_rate {d : Nat} (N alpha : Nat)
    (v : Nat -> (Fin d -> Real) -> Complex) (A : Nat -> Real) {b rho : Real}
    (halpha : alpha ≤ N + 1) (hA : ∀ k, 0 ≤ A k) (hb : 0 < b) (hrho : 0 < rho)
    (hv : ∀ k ∈ Finset.range (alpha + 1),
      RadiusProfileBound (v k) (A k * rho ^ (k : Real))
        (k + (N + 1 - (alpha - k))) (b * rho)) :
    (∑ k ∈ Finset.range (alpha + 1),
        Real.sqrt (∫ z : Fin d -> Real, ‖v k z‖ ^ 2))
      ≤ (∑ k ∈ Finset.range (alpha + 1),
            A k * Real.sqrt (gaussianMoment d (k + (N + 1 - (alpha - k))) (2 * b)))
        * rho ^ (-(((N : Real) - (alpha : Real) + 1) / 2) - (d : Real) / 4) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkle : k ≤ alpha := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hkj : k + (alpha - k) = alpha := Nat.add_sub_cancel' hkle
  have hjN : alpha - k ≤ N + 1 := le_trans (Nat.sub_le _ _) halpha
  exact reflectedBoundaryTerm_L2_rate hkj hjN (hA k) hb hrho (hv k hk)

/-- **The source's displayed rate.**  In the source's boundary dimension the
Gaussian factor is `3/4`, so the estimate above is literally the display
`|| v_rho ||_{H^k(R_1)} <= C rho^{-(N-k+1)/2 - 3/4}` of Subsection 3.2. -/
theorem reflectedBoundary_source_rate (N alpha : Nat)
    (v : Nat -> (Fin 3 -> Real) -> Complex) (A : Nat -> Real) {b rho : Real}
    (halpha : alpha ≤ N + 1) (hA : ∀ k, 0 ≤ A k) (hb : 0 < b) (hrho : 0 < rho)
    (hv : ∀ k ∈ Finset.range (alpha + 1),
      RadiusProfileBound (v k) (A k * rho ^ (k : Real))
        (k + (N + 1 - (alpha - k))) (b * rho)) :
    (∑ k ∈ Finset.range (alpha + 1),
        Real.sqrt (∫ z : Fin 3 -> Real, ‖v k z‖ ^ 2))
      ≤ (∑ k ∈ Finset.range (alpha + 1),
            A k * Real.sqrt (gaussianMoment 3 (k + (N + 1 - (alpha - k))) (2 * b)))
        * rho ^ (-(((N : Real) - (alpha : Real) + 1) / 2) - 3 / 4) := by
  have h := reflectedBoundary_summed_L2_rate (d := 3) N alpha v A halpha hA hb hrho hv
  norm_num at h
  exact h

/-! ## Sobolev-order bookkeeping

Each transverse derivative of a beam costs one power of the frequency, so the
`k`-th derivative jet satisfies a profile bound with constant `A_k rho^k`.  The
`L^2` rates then all sit below the top-order one as soon as `rho >= 1`, which
is the source's Sobolev-order bookkeeping.
-/

/-- **The Sobolev-order transverse rate.**  If the `k`-th derivative jet obeys a
profile bound with constant `A k * rho^k` for each `k <= K`, the sum of the
transverse `L^2` norms is `O(rho^{K - m - d/4})`. -/
theorem sobolevSum_L2_rate {d K : Nat}
    (u : Fin (K + 1) -> (Fin d -> Real) -> Complex) (A : Fin (K + 1) -> Real)
    {m : Nat} {b rho : Real}
    (hA : ∀ k, 0 ≤ A k) (hb : 0 < b) (hrho : 1 ≤ rho)
    (hu : ∀ k : Fin (K + 1),
      GaussianProfileBound (u k) (A k * rho ^ (((k : Nat) : Real))) m (b * rho)) :
    (∑ k, Real.sqrt (∫ z : Fin d -> Real, ‖u k z‖ ^ 2))
      ≤ (∑ k, A k) * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
          * rho ^ ((K : Real) - (m : Real) - (d : Real) / 4) := by
  have hrho0 : (0 : Real) < rho := lt_of_lt_of_le one_pos hrho
  have hMnn : (0 : Real) ≤ Real.sqrt (gaussianMoment d (2 * m) (2 * b)) :=
    Real.sqrt_nonneg _
  have hterm : ∀ k : Fin (K + 1),
      Real.sqrt (∫ z : Fin d -> Real, ‖u k z‖ ^ 2)
        ≤ A k * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
            * rho ^ ((K : Real) - (m : Real) - (d : Real) / 4) := by
    intro k
    have hk := beamProfile_L2_rate (hA k) hb hrho0 (hu k)
    refine hk.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hA k) hMnn)
    refine Real.rpow_le_rpow_of_exponent_le hrho ?_
    have hkK : ((k : Nat) : Real) ≤ (K : Real) := by
      exact_mod_cast Nat.lt_succ_iff.1 k.isLt
    linarith
  calc (∑ k, Real.sqrt (∫ z : Fin d -> Real, ‖u k z‖ ^ 2))
      ≤ ∑ k : Fin (K + 1), A k * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
          * rho ^ ((K : Real) - (m : Real) - (d : Real) / 4) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (∑ k, A k) * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
          * rho ^ ((K : Real) - (m : Real) - (d : Real) / 4) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]



/-! ## Instantiation at a Gaussian beam -/

/-- **A Gaussian beam satisfies the profile bound.**  If the phase has the
source's transverse coercivity `Im phi >= b |z|^2` and the amplitude is dominated
by `A |z|^{2m}`, then `e^{i rho phi} a` satisfies the profile bound with constant
`A` and frequency-scaled width `b rho`. -/
theorem profileBound_of_beam {d : Nat} {phi a : (Fin d -> Real) -> Complex}
    {A b rho : Real} {m : Nat} (hrho : 0 < rho)
    (hIm : ∀ z, b * radiusSq z ≤ (phi z).im)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    GaussianProfileBound
      (fun z => Complex.exp (Complex.I * (rho : Complex) * phi z) * a z) A m (b * rho) := by
  intro z
  have hre : (Complex.I * (rho : Complex) * phi z).re = -(rho * (phi z).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  have h1 : Real.exp (-(rho * (phi z).im)) ≤ Real.exp (-(b * rho) * radiusSq z) := by
    refine Real.exp_le_exp.2 ?_
    have h2 := mul_le_mul_of_nonneg_left (hIm z) hrho.le
    linarith
  have hstep : ‖Complex.exp (Complex.I * (rho : Complex) * phi z) * a z‖
      = Real.exp (-(rho * (phi z).im)) * ‖a z‖ := by
    rw [norm_mul, Complex.norm_exp, hre]
  rw [hstep]
  calc Real.exp (-(rho * (phi z).im)) * ‖a z‖
      ≤ Real.exp (-(b * rho) * radiusSq z) * (A * (radiusSq z) ^ m) :=
        mul_le_mul h1 (ha z) (norm_nonneg _) (Real.exp_pos _).le
    _ = A * (radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z) := by ring

/-- **The source's transverse boundary rate for an actual Gaussian beam.**
A beam whose phase is transversally coercive with constant `b` and whose
amplitude is dominated by `A |z|^{2m}` has transverse `L^2` norm bounded by
`A * (moment)^{1/2} * rho^{-(m + d/4)}`. -/
theorem beamProfile_L2_rate_of_beam {d : Nat} {phi a : (Fin d -> Real) -> Complex}
    {A b rho : Real} {m : Nat} (hA : 0 ≤ A) (hb : 0 < b) (hrho : 0 < rho)
    (hIm : ∀ z, b * radiusSq z ≤ (phi z).im)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    Real.sqrt (∫ z : Fin d -> Real,
        ‖Complex.exp (Complex.I * (rho : Complex) * phi z) * a z‖ ^ 2)
      ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) :=
  sqrt_integral_normSq_le_of_profileBound hA hb hrho (profileBound_of_beam hrho hIm ha)

/-- **A profile bound stated in the ambient norm becomes one in the Euclidean
radius**, at the cost of dividing the Gaussian width by the dimension. -/
theorem profileBound_of_normBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C w : Real} {m : Nat} (hd : 0 < d) (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hf : ∀ z, ‖f z‖ ≤ C * (‖z‖ ^ 2) ^ m * Real.exp (-w * ‖z‖ ^ 2)) :
    GaussianProfileBound f C m (w / (d : Real)) := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  intro z
  have hnorm := norm_sq_le_radiusSq z
  have hpow : (‖z‖ ^ 2) ^ m ≤ (radiusSq z) ^ m :=
    pow_le_pow_left₀ (sq_nonneg _) hnorm m
  have hexp : Real.exp (-w * ‖z‖ ^ 2)
      ≤ Real.exp (-(w / (d : Real)) * radiusSq z) := by
    refine Real.exp_le_exp.2 ?_
    have hcomp := radiusSq_le_dim_mul_norm_sq z
    have hscaled : (w / (d : Real)) * radiusSq z
        ≤ (w / (d : Real)) * ((d : Real) * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcomp (div_nonneg hw hdR.le)
    have hsimp : (w / (d : Real)) * ((d : Real) * ‖z‖ ^ 2) = w * ‖z‖ ^ 2 := by
      field_simp
    rw [hsimp] at hscaled
    linarith
  calc ‖f z‖ ≤ C * (‖z‖ ^ 2) ^ m * Real.exp (-w * ‖z‖ ^ 2) := hf z
    _ ≤ C * (radiusSq z) ^ m * Real.exp (-(w / (d : Real)) * radiusSq z) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hexp
          (Real.exp_pos _).le (mul_nonneg hC (pow_nonneg (radiusSq_nonneg z) m))

/-! ## The algebra of profile-bounded functions

The source multiplies four Gaussian beams before integrating; the widths then
add and so do the transverse weights.  The four lemmas below record exactly
that, so that the interaction integrand inherits a profile bound from the
individual beams rather than being assumed to have one.
-/

/-- Enlarging the constant preserves a profile bound. -/
theorem GaussianProfileBound.mono_const {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C C' : Real} {m : Nat} {w : Real} (hCC : C ≤ C')
    (hf : GaussianProfileBound f C m w) : GaussianProfileBound f C' m w := by
  intro z
  refine (hf z).trans ?_
  have hX : (0 : Real) ≤ (radiusSq z) ^ m := pow_nonneg (radiusSq_nonneg z) m
  have hE : (0 : Real) ≤ Real.exp (-w * radiusSq z) := (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hX) hE
  exact this

/-- Profile bounds add. -/
theorem GaussianProfileBound.add {d : Nat} {f g : (Fin d -> Real) -> Complex}
    {C₁ C₂ : Real} {m : Nat} {w : Real}
    (hf : GaussianProfileBound f C₁ m w) (hg : GaussianProfileBound g C₂ m w) :
    GaussianProfileBound (fun z => f z + g z) (C₁ + C₂) m w := by
  intro z
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C₁ * (radiusSq z) ^ m * Real.exp (-w * radiusSq z)
        + C₂ * (radiusSq z) ^ m * Real.exp (-w * radiusSq z) :=
      add_le_add (hf z) (hg z)
    _ = (C₁ + C₂) * (radiusSq z) ^ m * Real.exp (-w * radiusSq z) := by ring

/-- Profile bounds scale. -/
theorem GaussianProfileBound.const_mul {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {w : Real} (c : Complex)
    (hf : GaussianProfileBound f C m w) :
    GaussianProfileBound (fun z => c * f z) (‖c‖ * C) m w := by
  intro z
  rw [norm_mul]
  calc ‖c‖ * ‖f z‖
      ≤ ‖c‖ * (C * (radiusSq z) ^ m * Real.exp (-w * radiusSq z)) :=
        mul_le_mul_of_nonneg_left (hf z) (norm_nonneg c)
    _ = ‖c‖ * C * (radiusSq z) ^ m * Real.exp (-w * radiusSq z) := by ring

/-- **Profile bounds multiply: the widths add and so do the transverse
weights.**  This is the bookkeeping behind the source's four-beam product. -/
theorem GaussianProfileBound.mul {d : Nat} {f g : (Fin d -> Real) -> Complex}
    {C₁ C₂ : Real} {m₁ m₂ : Nat} {w₁ w₂ : Real}
    (hf : GaussianProfileBound f C₁ m₁ w₁) (hg : GaussianProfileBound g C₂ m₂ w₂) :
    GaussianProfileBound (fun z => f z * g z) (C₁ * C₂) (m₁ + m₂) (w₁ + w₂) := by
  intro z
  have hexp : Real.exp (-w₁ * radiusSq z) * Real.exp (-w₂ * radiusSq z)
      = Real.exp (-(w₁ + w₂) * radiusSq z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow : (radiusSq z) ^ m₁ * (radiusSq z) ^ m₂ = (radiusSq z) ^ (m₁ + m₂) :=
    (pow_add _ _ _).symm
  rw [norm_mul]
  calc ‖f z‖ * ‖g z‖
      ≤ (C₁ * (radiusSq z) ^ m₁ * Real.exp (-w₁ * radiusSq z))
          * (C₂ * (radiusSq z) ^ m₂ * Real.exp (-w₂ * radiusSq z)) :=
        mul_le_mul (hf z) (hg z) (norm_nonneg _) ((norm_nonneg (f z)).trans (hf z))
    _ = C₁ * C₂ * ((radiusSq z) ^ m₁ * (radiusSq z) ^ m₂)
          * (Real.exp (-w₁ * radiusSq z) * Real.exp (-w₂ * radiusSq z)) := by ring
    _ = C₁ * C₂ * (radiusSq z) ^ (m₁ + m₂) * Real.exp (-(w₁ + w₂) * radiusSq z) := by
        rw [hpow, hexp]

/-- **A finite product of profile-bounded functions is profile bounded**, with
the constants, transverse weights and Gaussian widths all multiplied resp.
summed.  Instantiated at a four-element index set this is exactly the source's
four-beam interaction integrand. -/
theorem profileBound_finsetProd {iota : Type} [DecidableEq iota] {d : Nat}
    (f : iota -> (Fin d -> Real) -> Complex) (C : iota -> Real) (m : iota -> Nat)
    (w : iota -> Real) (s : Finset iota)
    (h : ∀ j ∈ s, GaussianProfileBound (f j) (C j) (m j) (w j)) :
    GaussianProfileBound (fun z => ∏ j ∈ s, f j z) (∏ j ∈ s, C j) (∑ j ∈ s, m j)
      (∑ j ∈ s, w j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro z
      simp only
      simp
  | insert a s ha ih =>
      have hmem : ∀ j ∈ s, GaussianProfileBound (f j) (C j) (m j) (w j) :=
        fun j hj => h j (Finset.mem_insert_of_mem hj)
      have hprod := (h a (Finset.mem_insert_self a s)).mul (ih hmem)
      intro z
      simp only
      have hrw : (∏ j ∈ insert a s, f j z) = f a z * ∏ j ∈ s, f j z :=
        Finset.prod_insert ha
      rw [hrw, Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      exact hprod z

/-! ## The `L^1` companion: the interaction integral

The transverse `L^2` rate governs the boundary Sobolev estimate.  The source's
*interaction integral* -- the spacetime integral of the product of the four
beams against the unknown coefficient -- is instead controlled in `L^1`, where
the Gaussian width buys a full `rho^{-d/2}` rather than `rho^{-d/4}`.  Both
come from the same profile bound.
-/

/-- **The `L^1` form of the bridge.**  A profile-bounded function has
transverse `L^1` norm `O(rho^{-(m + d/2)})`. -/
theorem integral_norm_le_of_profileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {b rho : Real} (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f C m (b * rho)) :
    (∫ z : Fin d -> Real, ‖f z‖)
      ≤ C * (rho ^ (-((m : Real) + (d : Real) / 2)) * gaussianMoment d m b) := by
  have hbrho : (0 : Real) < b * rho := by positivity
  have hmaj : Integrable (fun z : Fin d -> Real =>
      C * ((radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z))) :=
    (integrable_moment_pi (d := d) m hbrho).const_mul _
  have hbound : ∀ z : Fin d -> Real, ‖f z‖
      ≤ C * ((radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z)) := by
    intro z
    have h := hf z
    rwa [mul_assoc] at h
  calc (∫ z : Fin d -> Real, ‖f z‖)
      ≤ ∫ z : Fin d -> Real,
          C * ((radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => norm_nonneg _) hmaj
          (Filter.Eventually.of_forall hbound)
    _ = C * ∫ z : Fin d -> Real,
          (radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z) :=
        MeasureTheory.integral_const_mul _ _
    _ = C * (rho ^ (-((m : Real) + (d : Real) / 2)) * gaussianMoment d m b) := by
        rw [integral_moment_scaledGaussian_pi (d := d) m hb hrho]

/-- **The interaction-integral bound.**  The transverse integral of a
profile-bounded function is `O(rho^{-(m + d/2)})`. -/
theorem norm_integral_le_of_profileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {b rho : Real} (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f C m (b * rho)) :
    ‖∫ z : Fin d -> Real, f z‖
      ≤ C * (rho ^ (-((m : Real) + (d : Real) / 2)) * gaussianMoment d m b) :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_le_of_profileBound hb hrho hf)

/-- A bounded weight -- the source's unknown coefficient -- multiplies the
profile bound by its sup bound. -/
theorem GaussianProfileBound.bounded_mul {d : Nat}
    {W f : (Fin d -> Real) -> Complex} {K C : Real} {m : Nat} {w : Real}
    (hW : ∀ z, ‖W z‖ ≤ K) (hf : GaussianProfileBound f C m w) :
    GaussianProfileBound (fun z => W z * f z) (K * C) m w := by
  have hK : (0 : Real) ≤ K := (norm_nonneg (W 0)).trans (hW 0)
  intro z
  rw [norm_mul]
  calc ‖W z‖ * ‖f z‖
      ≤ K * (C * (radiusSq z) ^ m * Real.exp (-w * radiusSq z)) :=
        mul_le_mul (hW z) (hf z) (norm_nonneg _) hK
    _ = K * C * (radiusSq z) ^ m * Real.exp (-w * radiusSq z) := by ring

/-- **The weighted four-beam interaction integral.**  With the source's unknown
coefficient bounded by `K`, the interaction integral obeys the same summed
rate, scaled by `K`. -/
theorem weightedFourBeamInteraction_bound {d : Nat}
    (W : (Fin d -> Real) -> Complex) (f : Fin 4 -> (Fin d -> Real) -> Complex)
    (K : Real) (C : Fin 4 -> Real) (m : Fin 4 -> Nat) (b : Fin 4 -> Real)
    {rho : Real} (hW : ∀ z, ‖W z‖ ≤ K)
    (hb : 0 < ∑ j, b j) (hrho : 0 < rho)
    (h : ∀ j, GaussianProfileBound (f j) (C j) (m j) (b j * rho)) :
    ‖∫ z : Fin d -> Real, W z * ∏ j, f j z‖
      ≤ K * (∏ j, C j)
          * (rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))
              * gaussianMoment d (∑ j, m j) (∑ j, b j)) := by
  have hsum : (∑ j, b j * rho) = (∑ j, b j) * rho := (Finset.sum_mul _ _ _).symm
  have hprod := profileBound_finsetProd f C m (fun j => b j * rho) Finset.univ
    (fun j _ => h j)
  rw [hsum] at hprod
  exact norm_integral_le_of_profileBound hb hrho (hprod.bounded_mul hW)

/-- **The four-beam interaction integral decays at the summed rate.**  With the
coercivity constants of the four phases adding and the transverse weights
adding, the source's interaction integral is
`O(rho^{-(m_0 + m_1 + m_2 + m_3 + d/2)})`. -/
theorem fourBeamInteraction_bound {d : Nat}
    (f : Fin 4 -> (Fin d -> Real) -> Complex) (C : Fin 4 -> Real)
    (m : Fin 4 -> Nat) (b : Fin 4 -> Real) {rho : Real}
    (hb : 0 < ∑ j, b j) (hrho : 0 < rho)
    (h : ∀ j, GaussianProfileBound (f j) (C j) (m j) (b j * rho)) :
    ‖∫ z : Fin d -> Real, ∏ j, f j z‖
      ≤ (∏ j, C j)
          * (rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))
              * gaussianMoment d (∑ j, m j) (∑ j, b j)) := by
  have hsum : (∑ j, b j * rho) = (∑ j, b j) * rho := (Finset.sum_mul _ _ _).symm
  have hbound := profileBound_finsetProd f C m (fun j => b j * rho) Finset.univ
    (fun j _ => h j)
  rw [hsum] at hbound
  exact norm_integral_le_of_profileBound hb hrho hbound

/-! ## Vanishing of the interaction remainder

`LiuWang2025SemilinearWaveEquation44RateRobustRecovery` recovers the unknown
coefficient from equation (4.4) using only that the beam-substitution remainder
*tends to zero* as `rho -> infinity`.  The quantitative bounds above discharge
that hypothesis: a profile-bounded interaction integral decays at a strictly
negative power of `rho`, hence to zero.
-/

/-- A quantity bounded eventually by `K rho^{-s}` with `s > 0` tends to zero. -/
theorem tendsto_zero_of_rpow_bound {R : Real -> Complex} {K s : Real}
    (hs : 0 < s)
    (hbound : ∀ᶠ rho in Filter.atTop, ‖R rho‖ ≤ K * rho ^ (-s)) :
    Filter.Tendsto R Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' hbound ?_
  have h := tendsto_rpow_neg_atTop hs
  simpa using h.const_mul K

/-- **The source's beam-substitution remainder vanishes.**  If the four beams
obey profile bounds uniform in the frequency and the unknown coefficient is
bounded, the weighted interaction integral tends to zero as `rho -> infinity`.
This is exactly the hypothesis consumed by the rate-robust equation-(4.4)
recovery, now supplied by a quantitative estimate rather than assumed. -/
theorem weightedFourBeamInteraction_tendsto_zero {d : Nat}
    (W : (Fin d -> Real) -> Complex)
    (u : Real -> Fin 4 -> (Fin d -> Real) -> Complex)
    (K : Real) (C : Fin 4 -> Real) (m : Fin 4 -> Nat) (b : Fin 4 -> Real)
    (hd : 0 < d) (hW : ∀ z, ‖W z‖ ≤ K) (hb : 0 < ∑ j, b j)
    (hu : ∀ rho : Real, 0 < rho ->
      ∀ j, GaussianProfileBound (u rho j) (C j) (m j) (b j * rho)) :
    Filter.Tendsto (fun rho : Real => ∫ z : Fin d -> Real, W z * ∏ j, u rho j z)
      Filter.atTop (nhds 0) := by
  have hs : (0 : Real) < ((∑ j, m j : Nat) : Real) + (d : Real) / 2 := by
    have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
    have hm : (0 : Real) ≤ ((∑ j, m j : Nat) : Real) := Nat.cast_nonneg _
    linarith
  refine tendsto_zero_of_rpow_bound
    (K := K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j)) hs ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with rho hrho
  have h := weightedFourBeamInteraction_bound W (u rho) K C m b hW hb hrho
    (hu rho hrho)
  refine h.trans_eq ?_
  ring

/-! ## The inaccessible-boundary pairing

Subsection 4.2 of the source bounds the surviving boundary term of equation
(4.3),

`| int_{Sigma \ Gamma} (d_nu U^{(1,123)} - d_nu U^{(2,123)}) w_0 dS_g dt |`,

by Cauchy--Schwarz against the reflected-beam estimate, concluding that it is
`O(rho^{-(N-k+1)/2 - 3/4})` and hence vanishes in the limit.  The normal
derivative jump has fixed finite `L^2` mass -- it is an `H^{s-3/2}` trace with
`s >= 5` -- while the beam's `L^2` mass decays at the rate just proved.

Balancing the elementary inequality `ab <= (t/2)a^2 + (1/(2t))b^2` at
`t = rho^{-E}` reproduces the Cauchy--Schwarz rate exactly, so the source's
conclusion follows with no loss.
-/

/-- The elementary inequality behind the source's Cauchy--Schwarz step. -/
theorem mul_le_half_sq_add {a b t : Real} (ht : 0 < t) :
    a * b ≤ t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 := by
  have hkey : (0 : Real) ≤ (t * a - b) ^ 2 := sq_nonneg _
  have hsplit : t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 - a * b
      = 1 / (2 * t) * (t * a - b) ^ 2 := by
    field_simp
    ring
  have hprod : (0 : Real) ≤ 1 / (2 * t) * (t * a - b) ^ 2 :=
    mul_nonneg (by positivity) hkey
  linarith [hsplit, hprod]

/-- The balanced bound for a bilinear boundary pairing. -/
theorem norm_integral_mul_le_balanced {d : Nat}
    (F w : (Fin d -> Real) -> Complex) {t : Real} (ht : 0 < t)
    (hF : Integrable (fun z : Fin d -> Real => ‖F z‖ ^ 2))
    (hw : Integrable (fun z : Fin d -> Real => ‖w z‖ ^ 2)) :
    ‖∫ z : Fin d -> Real, F z * w z‖
      ≤ t / 2 * (∫ z : Fin d -> Real, ‖F z‖ ^ 2)
        + 1 / (2 * t) * (∫ z : Fin d -> Real, ‖w z‖ ^ 2) := by
  have hmaj : Integrable (fun z : Fin d -> Real =>
      t / 2 * ‖F z‖ ^ 2 + 1 / (2 * t) * ‖w z‖ ^ 2) :=
    (hF.const_mul _).add (hw.const_mul _)
  have hpt : ∀ z : Fin d -> Real, ‖F z * w z‖
      ≤ t / 2 * ‖F z‖ ^ 2 + 1 / (2 * t) * ‖w z‖ ^ 2 := by
    intro z
    rw [norm_mul]
    exact mul_le_half_sq_add ht
  calc ‖∫ z : Fin d -> Real, F z * w z‖
      ≤ ∫ z : Fin d -> Real, ‖F z * w z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : Fin d -> Real, (t / 2 * ‖F z‖ ^ 2 + 1 / (2 * t) * ‖w z‖ ^ 2) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => norm_nonneg _) hmaj
          (Filter.Eventually.of_forall hpt)
    _ = t / 2 * (∫ z : Fin d -> Real, ‖F z‖ ^ 2)
          + 1 / (2 * t) * (∫ z : Fin d -> Real, ‖w z‖ ^ 2) := by
        rw [MeasureTheory.integral_add (hF.const_mul _) (hw.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **The source's inaccessible-boundary estimate.**  A pairing of a fixed
finite-`L^2`-mass trace against a beam whose `L^2` mass decays like
`rho^{-2E}` is `O(rho^{-E})` -- exactly the Cauchy--Schwarz rate, obtained here
by balancing at `t = rho^{-E}`. -/
theorem norm_integral_mul_le_rate {d : Nat}
    (F w : (Fin d -> Real) -> Complex) {P Cw E rho : Real}
    (_hE : 0 < E) (hrho : 0 < rho)
    (hF : Integrable (fun z : Fin d -> Real => ‖F z‖ ^ 2))
    (hFP : (∫ z : Fin d -> Real, ‖F z‖ ^ 2) ≤ P)
    (hw : Integrable (fun z : Fin d -> Real => ‖w z‖ ^ 2))
    (hwQ : (∫ z : Fin d -> Real, ‖w z‖ ^ 2) ≤ Cw ^ 2 * rho ^ (-(2 * E))) :
    ‖∫ z : Fin d -> Real, F z * w z‖ ≤ (P + Cw ^ 2) / 2 * rho ^ (-E) := by
  have ht : (0 : Real) < rho ^ (-E) := Real.rpow_pos_of_pos hrho _
  have hbal := norm_integral_mul_le_balanced F w ht hF hw
  have hinv : 1 / (2 * rho ^ (-E)) = rho ^ E / 2 := by
    rw [Real.rpow_neg hrho.le]
    field_simp
  have hcombine : rho ^ E * (rho ^ (-(2 * E))) = rho ^ (-E) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  have hstep1 : rho ^ (-E) / 2 * (∫ z : Fin d -> Real, ‖F z‖ ^ 2)
      ≤ rho ^ (-E) / 2 * P :=
    mul_le_mul_of_nonneg_left hFP (by positivity)
  have hstep2 : 1 / (2 * rho ^ (-E)) * (∫ z : Fin d -> Real, ‖w z‖ ^ 2)
      ≤ 1 / (2 * rho ^ (-E)) * (Cw ^ 2 * rho ^ (-(2 * E))) :=
    mul_le_mul_of_nonneg_left hwQ (by positivity)
  have hfinal : rho ^ (-E) / 2 * P
        + 1 / (2 * rho ^ (-E)) * (Cw ^ 2 * rho ^ (-(2 * E)))
      = (P + Cw ^ 2) / 2 * rho ^ (-E) := by
    rw [hinv]
    calc rho ^ (-E) / 2 * P + rho ^ E / 2 * (Cw ^ 2 * rho ^ (-(2 * E)))
        = rho ^ (-E) / 2 * P + Cw ^ 2 / 2 * (rho ^ E * rho ^ (-(2 * E))) := by ring
      _ = rho ^ (-E) / 2 * P + Cw ^ 2 / 2 * rho ^ (-E) := by rw [hcombine]
      _ = (P + Cw ^ 2) / 2 * rho ^ (-E) := by ring
  linarith [hbal, hstep1, hstep2, hfinal.le, hfinal.ge]

/-- **The inaccessible-boundary term vanishes.**  This is the conclusion the
source needs from its equation-(4.3) boundary term: the pairing tends to zero as
`rho -> infinity`. -/
theorem inaccessiblePairing_tendsto_zero {d : Nat}
    (F : (Fin d -> Real) -> Complex) (w : Real -> (Fin d -> Real) -> Complex)
    {P Cw E : Real} (hE : 0 < E)
    (hF : Integrable (fun z : Fin d -> Real => ‖F z‖ ^ 2))
    (hFP : (∫ z : Fin d -> Real, ‖F z‖ ^ 2) ≤ P)
    (hw : ∀ rho : Real, 0 < rho ->
      Integrable (fun z : Fin d -> Real => ‖w rho z‖ ^ 2))
    (hwQ : ∀ rho : Real, 0 < rho ->
      (∫ z : Fin d -> Real, ‖w rho z‖ ^ 2) ≤ Cw ^ 2 * rho ^ (-(2 * E))) :
    Filter.Tendsto (fun rho : Real => ∫ z : Fin d -> Real, F z * w rho z)
      Filter.atTop (nhds 0) := by
  refine tendsto_zero_of_rpow_bound (K := (P + Cw ^ 2) / 2) hE ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with rho hrho
  exact norm_integral_mul_le_rate F (w rho) hE hrho hF hFP (hw rho hrho)
    (hwQ rho hrho)

/-! ## Specular reflection in the transverse variable

The source's reflected beam is obtained by reversing the transverse Fermi
coordinate normal to the inaccessible face.  That map is a linear isometry of
the transverse slice, so it preserves the Gaussian profile exactly: the
reflected beam obeys the same pointwise bound and hence the same `L^2` rate,
and the incident-minus-reflected combination vanishes identically on the face.
-/

/-- Specular reflection of the transverse variable in the `i0`-th Fermi
coordinate. -/
def reflect {d : Nat} (i0 : Fin d) (z : Fin d -> Real) : Fin d -> Real :=
  Function.update z i0 (-(z i0))

/-- Specular reflection preserves the transverse radius. -/
theorem radiusSq_reflect {d : Nat} (i0 : Fin d) (z : Fin d -> Real) :
    radiusSq (reflect i0 z) = radiusSq z := by
  rw [radiusSq, radiusSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = i0
  · subst h
    simp [reflect]
  · simp [reflect, h]

/-- Specular reflection is an involution. -/
theorem reflect_reflect {d : Nat} (i0 : Fin d) (z : Fin d -> Real) :
    reflect i0 (reflect i0 z) = z := by
  funext i
  by_cases h : i = i0
  · subst h
    simp [reflect]
  · simp [reflect, h]

/-- On the reflecting face the reflection is the identity. -/
theorem reflect_of_eq_zero {d : Nat} {i0 : Fin d} {z : Fin d -> Real}
    (hz : z i0 = 0) : reflect i0 z = z := by
  funext i
  by_cases h : i = i0
  · subst h
    simp [reflect, hz]
  · simp [reflect, h]

/-- **The reflected beam obeys the same profile bound.** -/
theorem GaussianProfileBound.comp_reflect {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {w : Real} (i0 : Fin d)
    (hf : GaussianProfileBound f C m w) :
    GaussianProfileBound (fun z => f (reflect i0 z)) C m w := by
  intro z
  have h := hf (reflect i0 z)
  rwa [radiusSq_reflect] at h

/-- Profile bounds subtract. -/
theorem GaussianProfileBound.sub {d : Nat} {f g : (Fin d -> Real) -> Complex}
    {C₁ C₂ : Real} {m : Nat} {w : Real}
    (hf : GaussianProfileBound f C₁ m w) (hg : GaussianProfileBound g C₂ m w) :
    GaussianProfileBound (fun z => f z - g z) (C₁ + C₂) m w := by
  intro z
  calc ‖f z - g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_sub_le _ _
    _ ≤ C₁ * (radiusSq z) ^ m * Real.exp (-w * radiusSq z)
        + C₂ * (radiusSq z) ^ m * Real.exp (-w * radiusSq z) :=
      add_le_add (hf z) (hg z)
    _ = (C₁ + C₂) * (radiusSq z) ^ m * Real.exp (-w * radiusSq z) := by ring

/-- The incident-plus-reflected combination obeys the profile bound with the
constant doubled. -/
theorem reflectedSum_profileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {w : Real} (i0 : Fin d)
    (hf : GaussianProfileBound f C m w) :
    GaussianProfileBound (fun z => f z + f (reflect i0 z)) (C + C) m w :=
  hf.add (hf.comp_reflect i0)

/-- The incident-minus-reflected combination obeys the profile bound with the
constant doubled. -/
theorem reflectedDifference_profileBound {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {w : Real} (i0 : Fin d)
    (hf : GaussianProfileBound f C m w) :
    GaussianProfileBound (fun z => f z - f (reflect i0 z)) (C + C) m w :=
  hf.sub (hf.comp_reflect i0)

/-- **The reflected difference vanishes identically on the reflecting face**:
the Dirichlet condition of the source's reflected-beam construction. -/
theorem reflectedDifference_eq_zero_on_face {d : Nat} {i0 : Fin d}
    (f : (Fin d -> Real) -> Complex) {z : Fin d -> Real} (hz : z i0 = 0) :
    f z - f (reflect i0 z) = 0 := by
  rw [reflect_of_eq_zero hz, sub_self]

/-- On the reflecting face the reflected sum doubles the incident beam. -/
theorem reflectedSum_on_face {d : Nat} {i0 : Fin d}
    (f : (Fin d -> Real) -> Complex) {z : Fin d -> Real} (hz : z i0 = 0) :
    f z + f (reflect i0 z) = 2 * f z := by
  rw [reflect_of_eq_zero hz]
  ring

/-- **The reflected sum obeys the source's transverse `L^2` rate**, with the
constant doubled and the exponent unchanged. -/
theorem reflectedSum_L2_rate {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {b rho : Real} (i0 : Fin d)
    (hC : 0 ≤ C) (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f C m (b * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖f z + f (reflect i0 z)‖ ^ 2)
      ≤ (C + C) * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) :=
  sqrt_integral_normSq_le_of_profileBound (by linarith) hb hrho
    (reflectedSum_profileBound i0 hf)

/-- **The reflected difference obeys the source's transverse `L^2` rate.** -/
theorem reflectedDifference_L2_rate {d : Nat} {f : (Fin d -> Real) -> Complex}
    {C : Real} {m : Nat} {b rho : Real} (i0 : Fin d)
    (hC : 0 ≤ C) (hb : 0 < b) (hrho : 0 < rho)
    (hf : GaussianProfileBound f C m (b * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖f z - f (reflect i0 z)‖ ^ 2)
      ≤ (C + C) * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) :=
  sqrt_integral_normSq_le_of_profileBound (by linarith) hb hrho
    (reflectedDifference_profileBound i0 hf)

/-! ## The Gaussian-beam remainder rate -/

/-- The norm of the frequency weight `rho^{-N}`. -/
theorem norm_inv_pow_ofReal {rho : Real} (hrho : 0 < rho) (N : Nat) :
    ‖((rho : Complex) ^ N)⁻¹‖ = rho ^ (-(N : Real)) := by
  rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hrho.le,
    Real.rpow_neg hrho.le, Real.rpow_natCast]

/-- **The Gaussian-beam remainder rate.**  After the WKB cancellation the
residual is `rho^{-N}` times a beam whose amplitude is the terminal jet.  If the
terminal jet is dominated by `A |z|^{2m}` and the phase carries the source's
transverse coercivity, the residual has transverse `L^2` norm of order
`rho^{-(N + m + d/4)}`. -/
theorem beamRemainder_L2_rate {d : Nat} {phi a : (Fin d -> Real) -> Complex}
    {A b rho : Real} {m N : Nat} (hA : 0 ≤ A) (hb : 0 < b) (hrho : 0 < rho)
    (hIm : ∀ z, b * radiusSq z ≤ (phi z).im)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    Real.sqrt (∫ z : Fin d -> Real,
        ‖((rho : Complex) ^ N)⁻¹
            * (Complex.exp (Complex.I * (rho : Complex) * phi z) * a z)‖ ^ 2)
      ≤ A * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
          * rho ^ (-(N : Real) - (m : Real) - (d : Real) / 4) := by
  have hbase := profileBound_of_beam (A := A) (m := m) hrho hIm ha
  have hscaled := hbase.const_mul ((rho : Complex) ^ N)⁻¹
  rw [norm_inv_pow_ofReal hrho N, mul_comm (rho ^ (-(N : Real))) A] at hscaled
  exact beamProfile_L2_rate (k := -(N : Real)) hA hb hrho hscaled

/-! ## The four-beam interaction integrand -/

/-- **The transverse `L^2` rate of a finite product of Gaussian beams.**  If
each factor obeys a pointwise profile bound with constant `C j`, transverse
weight `m j` and coercivity `b j`, then the product obeys the source's rate
with the summed weight and the summed coercivity. -/
theorem profileBound_prod_L2_rate {iota : Type} [DecidableEq iota] {d : Nat}
    (f : iota -> (Fin d -> Real) -> Complex) (C : iota -> Real) (m : iota -> Nat)
    (b : iota -> Real) (s : Finset iota) {rho : Real}
    (hC : 0 ≤ ∏ j ∈ s, C j) (hb : 0 < ∑ j ∈ s, b j) (hrho : 0 < rho)
    (h : ∀ j ∈ s, GaussianProfileBound (f j) (C j) (m j) (b j * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖∏ j ∈ s, f j z‖ ^ 2)
      ≤ (∏ j ∈ s, C j)
          * rho ^ (-(((∑ j ∈ s, m j : Nat) : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * ∑ j ∈ s, m j) (2 * ∑ j ∈ s, b j)) := by
  have hsum : (∑ j ∈ s, b j * rho) = (∑ j ∈ s, b j) * rho := (Finset.sum_mul _ _ _).symm
  have hbound := profileBound_finsetProd f C m (fun j => b j * rho) s h
  rw [hsum] at hbound
  exact sqrt_integral_normSq_le_of_profileBound hC hb hrho hbound

/-- The four-beam specialisation: the source's interaction integrand
`u^0 u^1 u^2 u^3` has transverse `L^2` norm of order
`rho^{-(m_0 + m_1 + m_2 + m_3 + d/4)}`. -/
theorem fourBeamProduct_L2_rate {d : Nat}
    (f : Fin 4 -> (Fin d -> Real) -> Complex) (C : Fin 4 -> Real) (m : Fin 4 -> Nat)
    (b : Fin 4 -> Real) {rho : Real}
    (hC : 0 ≤ ∏ j, C j) (hb : 0 < ∑ j, b j) (hrho : 0 < rho)
    (h : ∀ j, GaussianProfileBound (f j) (C j) (m j) (b j * rho)) :
    Real.sqrt (∫ z : Fin d -> Real, ‖∏ j, f j z‖ ^ 2)
      ≤ (∏ j, C j)
          * rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * ∑ j, m j) (2 * ∑ j, b j)) :=
  profileBound_prod_L2_rate f C m b Finset.univ hC hb hrho (fun j _ => h j)

/-! ## The source's normalized interaction

Subsection 4.2 multiplies the integral identity by `rho^{(n+1)/2}` before
passing to the limit.  That normalization is exactly the one the Gaussian mass
supplies: in spacetime dimension `d = 1 + n` the interaction integral carries
`rho^{-d/2}`, so the normalized quantity stays bounded and the stationary-phase
limit is finite.
-/

/-- **The source's normalization is the right one.**  Multiplying the weighted
four-beam interaction integral by `rho^{d/2}` -- the source's `rho^{(n+1)/2}` --
leaves a quantity bounded uniformly in `rho >= 1`. -/
theorem normalized_interaction_bounded {d : Nat}
    (W : (Fin d -> Real) -> Complex) (f : Fin 4 -> (Fin d -> Real) -> Complex)
    (K : Real) (C : Fin 4 -> Real) (m : Fin 4 -> Nat) (b : Fin 4 -> Real)
    {rho : Real} (hW : ∀ z, ‖W z‖ ≤ K) (hb : 0 < ∑ j, b j) (hrho : 1 ≤ rho)
    (hCnn : 0 ≤ ∏ j, C j)
    (h : ∀ j, GaussianProfileBound (f j) (C j) (m j) (b j * rho)) :
    rho ^ ((d : Real) / 2) * ‖∫ z : Fin d -> Real, W z * ∏ j, f j z‖
      ≤ K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j) := by
  have hrho0 : (0 : Real) < rho := lt_of_lt_of_le one_pos hrho
  have hK : (0 : Real) ≤ K := (norm_nonneg (W 0)).trans (hW 0)
  have hMnn : (0 : Real) ≤ gaussianMoment d (∑ j, m j) (∑ j, b j) :=
    gaussianMoment_nonneg _ _ _
  have hbound := weightedFourBeamInteraction_bound W f K C m b hW hb hrho0 h
  have hnorm : (0 : Real) ≤ rho ^ ((d : Real) / 2) :=
    (Real.rpow_pos_of_pos hrho0 _).le
  have hstep := mul_le_mul_of_nonneg_left hbound hnorm
  refine hstep.trans ?_
  have hsplit : rho ^ ((d : Real) / 2)
        * (K * (∏ j, C j)
            * (rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))
                * gaussianMoment d (∑ j, m j) (∑ j, b j)))
      = (K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j))
          * rho ^ (-((∑ j, m j : Nat) : Real)) := by
    have hcomb : rho ^ ((d : Real) / 2)
          * rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))
        = rho ^ (-((∑ j, m j : Nat) : Real)) := by
      rw [← Real.rpow_add hrho0]
      congr 1
      ring
    calc rho ^ ((d : Real) / 2)
          * (K * (∏ j, C j)
              * (rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))
                  * gaussianMoment d (∑ j, m j) (∑ j, b j)))
        = (K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j))
            * (rho ^ ((d : Real) / 2)
                * rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))) := by ring
      _ = (K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j))
            * rho ^ (-((∑ j, m j : Nat) : Real)) := by rw [hcomb]
  rw [hsplit]
  have htail : rho ^ (-((∑ j, m j : Nat) : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrho
      (neg_nonpos.2 (Nat.cast_nonneg _))
  have hconst : (0 : Real) ≤ K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j) :=
    mul_nonneg (mul_nonneg hK hCnn) hMnn
  calc (K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j))
        * rho ^ (-((∑ j, m j : Nat) : Real))
      ≤ (K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j)) * 1 :=
        mul_le_mul_of_nonneg_left htail hconst
    _ = K * (∏ j, C j) * gaussianMoment d (∑ j, m j) (∑ j, b j) := mul_one _

/-! ## The Gaussian stationary-phase limit

Subsection 4.2 passes to the limit in
`rho^{(n+1)/2} int V_3 e^{i rho S} a^0 a^1 a^2 a^3` by stationary phase
(Hoermander 7.7.5), using the properties of `S` at the interaction point.  For
the Gaussian weight that the Riccati construction actually produces, that
mechanism is an *exact* rescaling followed by dominated convergence, and both
steps are elementary.  The limit is the amplitude at the beam centre times the
computed, strictly positive Gaussian constant.
-/

/-- The additive Haar dilation for a complex-valued integrand. -/
theorem integral_comp_smul_pi_complex {d : Nat} (G : (Fin d -> Real) -> Complex)
    {r : Real} (hr : 0 ≤ r) :
    (∫ z : Fin d -> Real, G (r • z))
      = ((r ^ d)⁻¹ : Real) • ∫ y : Fin d -> Real, G y := by
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (Fin d -> Real))) G r (hR := hr)
  rw [h, Module.finrank_fin_fun]
  rfl

/-- Pulling a complex constant out of the integral of a real-valued integrand.
Routed through the real-linear map `t |-> c * t` to stay clear of the ambient
`NormedSpace Real Complex` instance diamond. -/
theorem integral_const_mul_ofReal {d : Nat} (c : Complex)
    {e : (Fin d -> Real) -> Real} (he : Integrable e) :
    (∫ w : Fin d -> Real, c * ((e w : Real) : Complex))
      = c * ((∫ w : Fin d -> Real, e w : Real) : Complex) :=
  ContinuousLinearMap.integral_comp_comm
    ((ContinuousLinearMap.mul Real Complex c).comp Complex.ofRealCLM) he

/-- **The exact Gaussian rescaling identity.**  No limit is taken: the change of
variables `z = rho^{-1/2} w` turns the frequency-scaled Gaussian integral into a
fixed Gaussian integral whose amplitude is sampled at shrinking scale.  The
prefactor `(sqrt rho)^d` is the source's `rho^{(n+1)/2}`. -/
theorem rescaled_gaussian_integral {d : Nat} (g : (Fin d -> Real) -> Complex)
    {b rho : Real} (hrho : 0 < rho) :
    ((Real.sqrt rho ^ d : Real)) • (∫ y : Fin d -> Real,
        g y * ((Real.exp (-(b * rho) * radiusSq y) : Real) : Complex))
      = ∫ w : Fin d -> Real,
          g ((Real.sqrt rho)⁻¹ • w)
            * ((Real.exp (-b * radiusSq w) : Real) : Complex) := by
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have hr : (0 : Real) ≤ (Real.sqrt rho)⁻¹ := inv_nonneg.2 hsqrt.le
  have hrsq : ((Real.sqrt rho)⁻¹) ^ 2 = rho⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hrho.le]
  have hinv : (((Real.sqrt rho)⁻¹ : Real) ^ d)⁻¹ = Real.sqrt rho ^ d := by
    rw [inv_pow, inv_inv]
  have hpt : ∀ w : Fin d -> Real,
      g ((Real.sqrt rho)⁻¹ • w)
          * ((Real.exp (-(b * rho) * radiusSq ((Real.sqrt rho)⁻¹ • w)) : Real) : Complex)
        = g ((Real.sqrt rho)⁻¹ • w)
          * ((Real.exp (-b * radiusSq w) : Real) : Complex) := by
    intro w
    have harg : -(b * rho) * radiusSq ((Real.sqrt rho)⁻¹ • w)
        = -b * radiusSq w := by
      rw [radiusSq_smul, hrsq]
      field_simp
    rw [harg]
  have h := integral_comp_smul_pi_complex
    (fun y : Fin d -> Real =>
      g y * ((Real.exp (-(b * rho) * radiusSq y) : Real) : Complex)) hr
  simp only at h
  rw [hinv] at h
  rw [← h]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- The computed Gaussian mass in the form the limit produces. -/
theorem integral_gaussian_pi_eq {d : Nat} {b : Real} (hb : 0 < b) :
    (∫ w : Fin d -> Real, Real.exp (-b * radiusSq w))
      = Real.sqrt (Real.pi / b) ^ d := by
  have h := gaussianMoment_zero d hb
  rw [gaussianMoment] at h
  simpa using h

/-- **Dominated convergence at shrinking scale.**  A bounded continuous
amplitude sampled at scale `rho^{-1/2}` against a fixed Gaussian converges to
its value at the beam centre. -/
theorem tendsto_rescaled_gaussian {d : Nat} (g : (Fin d -> Real) -> Complex)
    {A b : Real} (hg : Continuous g) (hA : ∀ z, ‖g z‖ ≤ A) (hb : 0 < b) :
    Filter.Tendsto
      (fun rho : Real => ∫ w : Fin d -> Real,
          g ((Real.sqrt rho)⁻¹ • w)
            * ((Real.exp (-b * radiusSq w) : Real) : Complex))
      Filter.atTop
      (nhds (g 0 * ((Real.sqrt (Real.pi / b) ^ d : Real) : Complex))) := by
  have hgauss : Continuous
      (fun w : Fin d -> Real => ((Real.exp (-b * radiusSq w) : Real) : Complex)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_radiusSq))
  have hgaussInt : Integrable (fun w : Fin d -> Real => Real.exp (-b * radiusSq w)) :=
    integrable_gaussian_pi (d := d) hb
  have hbound_int :
      Integrable (fun w : Fin d -> Real => Real.exp (-b * radiusSq w) * A) :=
    hgaussInt.mul_const _
  have hkey := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Fin d -> Real)))
    (l := (Filter.atTop : Filter Real))
    (F := fun rho : Real => fun w : Fin d -> Real =>
      g ((Real.sqrt rho)⁻¹ • w) * ((Real.exp (-b * radiusSq w) : Real) : Complex))
    (f := fun w : Fin d -> Real =>
      g 0 * ((Real.exp (-b * radiusSq w) : Real) : Complex))
    (bound := fun w : Fin d -> Real => Real.exp (-b * radiusSq w) * A)
    (Filter.Eventually.of_forall fun rho =>
      ((hg.comp (continuous_const_smul ((Real.sqrt rho)⁻¹))).mul
        hgauss).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun rho =>
      Filter.Eventually.of_forall fun w => by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
        exact mul_le_mul_of_nonneg_left (hA _) (Real.exp_pos _).le)
    hbound_int
    (Filter.Eventually.of_forall fun w => by
      have hsmul : Filter.Tendsto
          (fun rho : Real => (Real.sqrt rho)⁻¹ • w) Filter.atTop
          (nhds ((0 : Real) • w)) :=
        Filter.Tendsto.smul_const
          (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop) w
      rw [zero_smul] at hsmul
      exact ((hg.tendsto (0 : Fin d -> Real)).comp hsmul).mul_const _)
  rw [integral_const_mul_ofReal (g 0) hgaussInt, integral_gaussian_pi_eq hb] at hkey
  exact hkey

/-- **The source's stationary-phase endpoint for the Gaussian weight.**  The
normalized integral converges to the amplitude at the beam centre times the
computed Gaussian constant `sqrt(pi/b)^d`. -/
theorem tendsto_normalized_gaussian_integral {d : Nat}
    (g : (Fin d -> Real) -> Complex) {A b : Real}
    (hg : Continuous g) (hA : ∀ z, ‖g z‖ ≤ A) (hb : 0 < b) :
    Filter.Tendsto
      (fun rho : Real => ((Real.sqrt rho ^ d : Real)) • ∫ y : Fin d -> Real,
          g y * ((Real.exp (-(b * rho) * radiusSq y) : Real) : Complex))
      Filter.atTop
      (nhds (g 0 * ((Real.sqrt (Real.pi / b) ^ d : Real) : Complex))) := by
  have heq : (fun rho : Real => ∫ w : Fin d -> Real,
        g ((Real.sqrt rho)⁻¹ • w)
          * ((Real.exp (-b * radiusSq w) : Real) : Complex))
      =ᶠ[Filter.atTop] (fun rho : Real => ((Real.sqrt rho ^ d : Real)) •
        ∫ y : Fin d -> Real,
          g y * ((Real.exp (-(b * rho) * radiusSq y) : Real) : Complex)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with rho hrho
    exact (rescaled_gaussian_integral g hrho).symm
  exact (tendsto_rescaled_gaussian g hg hA hb).congr' heq

/-- The limiting constant is strictly positive, so the stationary-phase limit
vanishes exactly when the amplitude vanishes at the beam centre.  This is what
turns the source's limit identity into the pointwise conclusion `V_3(p~) = 0`. -/
theorem gaussianStationaryLimit_eq_zero_iff {d : Nat} {b : Real} (hb : 0 < b)
    (v : Complex) :
    v * ((Real.sqrt (Real.pi / b) ^ d : Real) : Complex) = 0 ↔ v = 0 := by
  have hpos : (0 : Real) < Real.sqrt (Real.pi / b) ^ d :=
    pow_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos hb)) d
  have hne : ((Real.sqrt (Real.pi / b) ^ d : Real) : Complex) ≠ 0 := by
    exact_mod_cast hpos.ne'
  rw [mul_eq_zero]
  exact or_iff_left hne

/-- **The source's pointwise conclusion, with no stationary-phase hypothesis.**
If the source's normalized identity holds with a boundary side that vanishes in
the limit -- which is exactly what the reflected-beam estimate supplies -- then
the amplitude vanishes at the interaction point.  For the Gaussian weight the
Riccati construction produces, both limits are theorems, so this is the paper's
`V_3(p~) = 0` with every analytic input discharged. -/
theorem amplitude_eq_zero_of_gaussian_identity {d : Nat}
    (g : (Fin d -> Real) -> Complex) {A b : Real}
    (hg : Continuous g) (hA : ∀ z, ‖g z‖ ≤ A) (hb : 0 < b)
    (boundary : Real -> Complex)
    (hbdry : Filter.Tendsto boundary Filter.atTop (nhds 0))
    (hid : ∀ rho : Real,
      ((Real.sqrt rho ^ d : Real)) • (∫ y : Fin d -> Real,
          g y * ((Real.exp (-(b * rho) * radiusSq y) : Real) : Complex))
        = boundary rho) :
    g 0 = 0 := by
  have h1 := tendsto_normalized_gaussian_integral g hg hA hb
  rw [funext hid] at h1
  exact (gaussianStationaryLimit_eq_zero_iff hb (g 0)).1
    (tendsto_nhds_unique h1 hbdry)

/-- **The source's pointwise conclusion for the actual interaction integrand.**
The amplitude in the source's identity is not arbitrary: it is the unknown
coefficient times the product of the beam amplitudes.  Since the source's
geodesics meet only at the interaction point, that product is nonzero there, so
the coefficient itself vanishes.  Stated over an arbitrary finite index so that
it covers both the cubic configuration of Subsection 4.2 and the
`m`-beam configuration of Subsection 4.3. -/
theorem coefficient_eq_zero_of_gaussian_identity {d : Nat} {iota : Type}
    [Fintype iota] (V : (Fin d -> Real) -> Complex)
    (a : iota -> (Fin d -> Real) -> Complex) {KV b : Real} {Ka : iota -> Real}
    (hV : Continuous V) (ha : ∀ j, Continuous (a j))
    (hVb : ∀ z, ‖V z‖ ≤ KV) (hab : ∀ j z, ‖a j z‖ ≤ Ka j)
    (hprod : (∏ j, a j 0) ≠ 0) (hb : 0 < b)
    (boundary : Real -> Complex)
    (hbdry : Filter.Tendsto boundary Filter.atTop (nhds 0))
    (hid : ∀ rho : Real,
      ((Real.sqrt rho ^ d : Real)) • (∫ y : Fin d -> Real,
          (V y * ∏ j, a j y)
            * ((Real.exp (-(b * rho) * radiusSq y) : Real) : Complex))
        = boundary rho) :
    V 0 = 0 := by
  have hcont : Continuous (fun z : Fin d -> Real => V z * ∏ j, a j z) :=
    hV.mul (continuous_finset_prod _ fun j _ => (ha j))
  have hKV : (0 : Real) ≤ KV := (norm_nonneg (V 0)).trans (hVb 0)
  have hbound : ∀ z : Fin d -> Real, ‖V z * ∏ j, a j z‖ ≤ KV * ∏ j, Ka j := by
    intro z
    rw [norm_mul, norm_prod]
    refine mul_le_mul (hVb z) ?_
      (Finset.prod_nonneg fun j _ => norm_nonneg _) hKV
    exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hab j z)
  have h := amplitude_eq_zero_of_gaussian_identity
    (fun z : Fin d -> Real => V z * ∏ j, a j z) hcont hbound hb boundary hbdry hid
  simp only at h
  exact (mul_eq_zero.1 h).resolve_right hprod

/-! ## The source's point recovery

Subsection 4.2 concludes by letting `rho -> infinity` in the integral identity
(4.3).  The left-hand side converges to a nonzero multiple of
`V_3(p~) a^0 a^1 a^2 a^3 (p~)` by stationary phase; the right-hand side -- the
term over the inaccessible face `Sigma \ Gamma` -- converges to zero.  Since the
stationary constant and the amplitude product are nonzero near `p~`, the
coefficient vanishes there.

The packet below is that argument with the *inaccessible-boundary limit supplied
rather than assumed*: it is a consequence of the reflected-beam `L^2` rate.  The
stationary-phase convergence of the principal term remains a hypothesis, to be
supplied by the complex stationary-phase layer.
-/

/-- The source's equation-(4.3) point-recovery packet, with the boundary term
realised as an actual pairing against the reflected beam. -/
structure ReflectedBeamPointRecovery (d : Nat) where
  /-- The unknown coefficient at the interaction point. -/
  coefficient : Complex
  /-- The nonzero stationary-phase constant. -/
  stationaryConstant : Complex
  /-- The product of the four beam amplitudes at the interaction point. -/
  amplitudeProduct : Complex
  /-- The normalized principal part of the identity. -/
  principal : Real -> Complex
  /-- The stationary-phase error. -/
  error : Real -> Complex
  /-- The normal-derivative jump on the inaccessible face. -/
  trace : (Fin d -> Real) -> Complex
  /-- The reflected beam restricted to the inaccessible face. -/
  beam : Real -> (Fin d -> Real) -> Complex
  /-- A bound for the fixed `L^2` mass of the trace. -/
  traceMass : Real
  /-- The constant in the reflected-beam `L^2` rate. -/
  beamConstant : Real
  /-- The positive rate of the reflected-beam estimate. -/
  rate : Real
  rate_pos : 0 < rate
  trace_integrable :
    Integrable (fun z : Fin d -> Real => ‖trace z‖ ^ 2)
  trace_mass_le : (∫ z : Fin d -> Real, ‖trace z‖ ^ 2) ≤ traceMass
  beam_integrable : ∀ rho : Real, 0 < rho ->
    Integrable (fun z : Fin d -> Real => ‖beam rho z‖ ^ 2)
  beam_mass_le : ∀ rho : Real, 0 < rho ->
    (∫ z : Fin d -> Real, ‖beam rho z‖ ^ 2) ≤ beamConstant ^ 2 * rho ^ (-(2 * rate))
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  amplitudeProduct_ne_zero : amplitudeProduct ≠ 0
  principal_tendsto : Filter.Tendsto principal Filter.atTop
    (nhds (stationaryConstant * coefficient * amplitudeProduct))
  error_tendsto_zero : Filter.Tendsto error Filter.atTop (nhds 0)
  integralIdentity : ∀ rho : Real,
    principal rho + error rho = ∫ z : Fin d -> Real, trace z * beam rho z

namespace ReflectedBeamPointRecovery

variable {d : Nat}

/-- **The inaccessible-boundary term vanishes** -- a theorem, from the
reflected-beam `L^2` rate, not a hypothesis. -/
theorem boundary_tendsto_zero (D : ReflectedBeamPointRecovery d) :
    Filter.Tendsto (fun rho : Real => ∫ z : Fin d -> Real, D.trace z * D.beam rho z)
      Filter.atTop (nhds 0) :=
  inaccessiblePairing_tendsto_zero D.trace D.beam D.rate_pos D.trace_integrable
    D.trace_mass_le D.beam_integrable D.beam_mass_le

/-- **The source's recovery at the interaction point.**  Both sides of the
identity converge; the boundary side converges to zero; the stationary constant
and the amplitude product are nonzero; hence the coefficient vanishes. -/
theorem coefficient_eq_zero (D : ReflectedBeamPointRecovery d) :
    D.coefficient = 0 := by
  have hsum : Filter.Tendsto (fun rho : Real => D.principal rho + D.error rho)
      Filter.atTop
      (nhds (D.stationaryConstant * D.coefficient * D.amplitudeProduct + 0)) :=
    D.principal_tendsto.add D.error_tendsto_zero
  rw [add_zero] at hsum
  have heq : (fun rho : Real => D.principal rho + D.error rho)
      = fun rho : Real => ∫ z : Fin d -> Real, D.trace z * D.beam rho z :=
    funext D.integralIdentity
  rw [heq] at hsum
  have hzero : D.stationaryConstant * D.coefficient * D.amplitudeProduct = 0 :=
    tendsto_nhds_unique hsum D.boundary_tendsto_zero
  have h1 : D.stationaryConstant * D.coefficient = 0 :=
    (mul_eq_zero.1 hzero).resolve_right D.amplitudeProduct_ne_zero
  exact (mul_eq_zero.1 h1).resolve_left D.stationaryConstant_ne_zero

/-- One reviewable object for the source's point recovery. -/
structure Certificate (D : ReflectedBeamPointRecovery d) : Prop where
  inaccessibleBoundaryVanishes :
    Filter.Tendsto (fun rho : Real => ∫ z : Fin d -> Real, D.trace z * D.beam rho z)
      Filter.atTop (nhds 0)
  coefficientZero : D.coefficient = 0

/-- Both fields are theorems. -/
def certificate (D : ReflectedBeamPointRecovery d) : Certificate D where
  inaccessibleBoundaryVanishes := D.boundary_tendsto_zero
  coefficientZero := D.coefficient_eq_zero

end ReflectedBeamPointRecovery

/-! ### Non-vacuity of the point-recovery packet -/

/-- A fixed square-integrable transverse profile. -/
def witnessProfile {d : Nat} (z : Fin d -> Real) : Complex :=
  Complex.exp (((-(radiusSq z) : Real) : Complex))

theorem norm_witnessProfile {d : Nat} (z : Fin d -> Real) :
    ‖witnessProfile z‖ = Real.exp (-(radiusSq z)) := by
  rw [witnessProfile, Complex.norm_exp, Complex.ofReal_re]

theorem witnessProfile_ne_zero {d : Nat} (z : Fin d -> Real) :
    witnessProfile z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_witnessProfile]
  exact (Real.exp_pos _).ne'

theorem normSq_witnessProfile {d : Nat} (z : Fin d -> Real) :
    ‖witnessProfile z‖ ^ 2 = Real.exp (-2 * radiusSq z) := by
  rw [norm_witnessProfile, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem integrable_witnessProfile {d : Nat} :
    Integrable (fun z : Fin d -> Real => ‖witnessProfile z‖ ^ 2) := by
  have h : (fun z : Fin d -> Real => ‖witnessProfile z‖ ^ 2)
      = fun z : Fin d -> Real => Real.exp (-2 * radiusSq z) :=
    funext normSq_witnessProfile
  rw [h]
  exact integrable_gaussian_pi (by norm_num)

/-- The `L^2` mass of the witness profile. -/
def witnessMass (d : Nat) : Real :=
  ∫ z : Fin d -> Real, ‖witnessProfile z‖ ^ 2

theorem witnessMass_nonneg (d : Nat) : 0 ≤ witnessMass d :=
  integral_nonneg fun _ => sq_nonneg _

/-- The witness beam: a fixed profile damped by one power of the frequency. -/
def witnessBeam {d : Nat} (rho : Real) (z : Fin d -> Real) : Complex :=
  ((rho : Complex))⁻¹ * witnessProfile z

theorem normSq_witnessBeam {d : Nat} {rho : Real} (hrho : 0 < rho)
    (z : Fin d -> Real) :
    ‖witnessBeam rho z‖ ^ 2 = (rho ^ 2)⁻¹ * ‖witnessProfile z‖ ^ 2 := by
  rw [witnessBeam, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hrho.le, mul_pow, inv_pow]

theorem integrable_witnessBeam {d : Nat} {rho : Real} (hrho : 0 < rho) :
    Integrable (fun z : Fin d -> Real => ‖witnessBeam rho z‖ ^ 2) := by
  have h : (fun z : Fin d -> Real => ‖witnessBeam rho z‖ ^ 2)
      = fun z : Fin d -> Real => (rho ^ 2)⁻¹ * ‖witnessProfile z‖ ^ 2 :=
    funext (normSq_witnessBeam hrho)
  rw [h]
  exact integrable_witnessProfile.const_mul _

theorem witnessBeam_mass_le {d : Nat} {rho : Real} (hrho : 0 < rho) :
    (∫ z : Fin d -> Real, ‖witnessBeam rho z‖ ^ 2)
      ≤ (Real.sqrt (witnessMass d)) ^ 2 * rho ^ (-(2 * (1 : Real))) := by
  have h : (fun z : Fin d -> Real => ‖witnessBeam rho z‖ ^ 2)
      = fun z : Fin d -> Real => (rho ^ 2)⁻¹ * ‖witnessProfile z‖ ^ 2 :=
    funext (normSq_witnessBeam hrho)
  have hexp : rho ^ (-(2 * (1 : Real))) = (rho ^ 2)⁻¹ := by
    rw [show -(2 * (1 : Real)) = -(2 : Real) by ring, Real.rpow_neg hrho.le]
    congr 1
    rw [show (2 : Real) = ((2 : Nat) : Real) by norm_num, Real.rpow_natCast]
  rw [h, MeasureTheory.integral_const_mul, Real.sq_sqrt (witnessMass_nonneg d),
    hexp, witnessMass]
  exact le_of_eq (mul_comm _ _)

/-- **The point-recovery packet is inhabited** by data with a genuinely nonzero
trace, a genuinely decaying beam, and genuine integrals. -/
def witnessPointRecovery (d : Nat) : ReflectedBeamPointRecovery d where
  coefficient := 0
  stationaryConstant := 1
  amplitudeProduct := 1
  principal := fun rho =>
    ∫ z : Fin d -> Real, witnessProfile z * witnessBeam rho z
  error := fun _ => 0
  trace := witnessProfile
  beam := witnessBeam
  traceMass := witnessMass d
  beamConstant := Real.sqrt (witnessMass d)
  rate := 1
  rate_pos := one_pos
  trace_integrable := integrable_witnessProfile
  trace_mass_le := le_of_eq rfl
  beam_integrable := fun _ hrho => integrable_witnessBeam hrho
  beam_mass_le := fun _ hrho => witnessBeam_mass_le hrho
  stationaryConstant_ne_zero := one_ne_zero
  amplitudeProduct_ne_zero := one_ne_zero
  principal_tendsto := by
    simpa using
      inaccessiblePairing_tendsto_zero (d := d) witnessProfile witnessBeam one_pos
        integrable_witnessProfile (le_of_eq rfl)
        (fun _ hrho => integrable_witnessBeam hrho)
        (fun _ hrho => witnessBeam_mass_le hrho)
  error_tendsto_zero := tendsto_const_nhds
  integralIdentity := fun _ => add_zero _

/-- The witness carries a nonvanishing trace, so the packet is not degenerate. -/
theorem witnessPointRecovery_trace_ne_zero (d : Nat) (z : Fin d -> Real) :
    (witnessPointRecovery d).trace z ≠ 0 :=
  witnessProfile_ne_zero z

/-! ## Non-vacuity -/

/-- A concrete beam satisfying the hypotheses: phase `i b |z|^2`, amplitude `1`. -/
theorem gaussianWitness_coercive {d : Nat} (b : Real) (z : Fin d -> Real) :
    b * radiusSq z
      ≤ (Complex.I * (b : Complex) * ((radiusSq z : Real) : Complex)).im := by
  simp [Complex.mul_re, Complex.mul_im]

/-- The witness amplitude is dominated with `A = 1`, `m = 0`. -/
theorem gaussianWitness_amplitude {d : Nat} (z : Fin d -> Real) :
    ‖(1 : Complex)‖ ≤ 1 * (radiusSq z) ^ 0 := by
  simp

/-- **The rate is realised.**  The concrete beam `e^{i rho (i b |z|^2)}` obeys the
transverse `L^2` rate with a strictly positive computed constant. -/
theorem gaussianWitness_L2_rate {d : Nat} {b rho : Real} (hb : 0 < b) (hrho : 0 < rho) :
    Real.sqrt (∫ z : Fin d -> Real,
        ‖Complex.exp (Complex.I * (rho : Complex)
            * (Complex.I * (b : Complex) * ((radiusSq z : Real) : Complex))) * 1‖ ^ 2)
      ≤ rho ^ (-((d : Real) / 4)) * Real.sqrt (gaussianMoment d 0 (2 * b)) := by
  have h := beamProfile_L2_rate_of_beam (d := d) (A := 1) (m := 0) (b := b) (rho := rho)
    zero_le_one hb hrho (fun z => gaussianWitness_coercive b z)
    (fun z => gaussianWitness_amplitude z)
  simpa using h

/-- The constant appearing in the witness rate is strictly positive. -/
theorem gaussianWitness_constant_pos {d : Nat} {b : Real} (hb : 0 < b) :
    0 < Real.sqrt (gaussianMoment d 0 (2 * b)) :=
  Real.sqrt_pos.2 (gaussianMoment_zero_pos d (by linarith))

/-! ## The reviewable certificate -/

/-- One reviewable object: the pointwise-to-`L^2` bridge in the transverse
variable, together with the computed moment scaling it rests on. -/
structure Certificate (d : Nat) (b rho : Real) : Prop where
  momentScaling : 0 < b -> 0 < rho -> ∀ m : Nat,
    (∫ z : Fin d -> Real, (radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z))
      = rho ^ (-((m : Real) + (d : Real) / 2)) * gaussianMoment d m b
  majorantIntegrable : 0 < b -> 0 < rho -> ∀ m : Nat,
    Integrable
      (fun z : Fin d -> Real => (radiusSq z) ^ m * Real.exp (-(b * rho) * radiusSq z))
  pointwiseToL2 : 0 < b -> 0 < rho ->
    ∀ (f : (Fin d -> Real) -> Complex) (C : Real) (m : Nat), 0 ≤ C ->
      GaussianProfileBound f C m (b * rho) ->
        Real.sqrt (∫ z : Fin d -> Real, ‖f z‖ ^ 2)
          ≤ C * rho ^ (-((m : Real) + (d : Real) / 4))
              * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
  beamRate : 0 < b -> 0 < rho ->
    ∀ (phi a : (Fin d -> Real) -> Complex) (A : Real) (m : Nat), 0 ≤ A ->
      (∀ z, b * radiusSq z ≤ (phi z).im) ->
      (∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) ->
        Real.sqrt (∫ z : Fin d -> Real,
            ‖Complex.exp (Complex.I * (rho : Complex) * phi z) * a z‖ ^ 2)
          ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
              * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
  interactionRate : 0 < b -> 0 < rho ->
    ∀ (f : (Fin d -> Real) -> Complex) (C : Real) (m : Nat),
      GaussianProfileBound f C m (b * rho) ->
        ‖∫ z : Fin d -> Real, f z‖
          ≤ C * (rho ^ (-((m : Real) + (d : Real) / 2)) * gaussianMoment d m b)
  productRate : 0 < rho -> ∀ (f : Fin 4 -> (Fin d -> Real) -> Complex)
    (C : Fin 4 -> Real) (m : Fin 4 -> Nat) (bs : Fin 4 -> Real),
      0 < (∑ j, bs j) ->
      (∀ j, GaussianProfileBound (f j) (C j) (m j) (bs j * rho)) ->
        ‖∫ z : Fin d -> Real, ∏ j, f j z‖
          ≤ (∏ j, C j)
            * (rho ^ (-(((∑ j, m j : Nat) : Real) + (d : Real) / 2))
                * gaussianMoment d (∑ j, m j) (∑ j, bs j))
  reflectedRate : 0 < b -> 0 < rho ->
    ∀ (f : (Fin d -> Real) -> Complex) (C : Real) (m : Nat) (i0 : Fin d), 0 ≤ C ->
      GaussianProfileBound f C m (b * rho) ->
        Real.sqrt (∫ z : Fin d -> Real, ‖f z - f (reflect i0 z)‖ ^ 2)
          ≤ (C + C) * rho ^ (-((m : Real) + (d : Real) / 4))
              * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
  remainderRate : 0 < b -> 0 < rho ->
    ∀ (phi a : (Fin d -> Real) -> Complex) (A : Real) (m N : Nat), 0 ≤ A ->
      (∀ z, b * radiusSq z ≤ (phi z).im) ->
      (∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) ->
        Real.sqrt (∫ z : Fin d -> Real,
            ‖((rho : Complex) ^ N)⁻¹
              * (Complex.exp (Complex.I * (rho : Complex) * phi z) * a z)‖ ^ 2)
          ≤ A * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
              * rho ^ (-(N : Real) - (m : Real) - (d : Real) / 4)
  normalization : 0 < b -> gaussianMoment d 0 b = Real.sqrt (Real.pi / b) ^ d
  nonVacuous : 0 < b -> 0 < Real.sqrt (gaussianMoment d 0 (2 * b))

/-- Every field of the bridge certificate is a theorem. -/
def certificate (d : Nat) (b rho : Real) : Certificate d b rho where
  momentScaling := fun hb hrho m => integral_moment_scaledGaussian_pi m hb hrho
  majorantIntegrable := fun hb hrho m =>
    integrable_moment_pi m (by positivity)
  pointwiseToL2 := fun hb hrho _f _C _m hC hbound =>
    sqrt_integral_normSq_le_of_profileBound hC hb hrho hbound
  beamRate := fun hb hrho _phi _a _A _m hA hIm ha =>
    beamProfile_L2_rate_of_beam hA hb hrho hIm ha
  interactionRate := fun hb hrho _f _C _m hbound =>
    norm_integral_le_of_profileBound hb hrho hbound
  productRate := fun hrho f C m bs hbs hj =>
    fourBeamInteraction_bound f C m bs hbs hrho hj
  reflectedRate := fun hb hrho _f _C _m i0 hC hbound =>
    reflectedDifference_L2_rate i0 hC hb hrho hbound
  remainderRate := fun hb hrho _phi _a _A _m _N hA hIm ha =>
    beamRemainder_L2_rate hA hb hrho hIm ha
  normalization := fun hb => gaussianMoment_zero d hb
  nonVacuous := fun hb => gaussianWitness_constant_pos hb

end LiuWang2025SemilinearWaveGaussianL2Bridge
