/-
Copyright (c) 2026.  Released under Apache 2.0.

# Complex stationary phase near one nondegenerate interaction point, for ρ-dependent amplitudes

This file proves the **analytic localization step** behind equation (4.4) of

  B. Liu and W. Wang, *On a partial data inverse problem for the semi-linear wave equation*,
  arXiv:2511.08794v1, Section 4.2,

for a `ρ`-indexed family of amplitudes (`LiuWang.AmplitudeFamily`), which is what the
Gaussian-beam amplitudes `a⁽ʲ⁾_{κⱼ,ρ}` of that paper actually are.

The results are deliberately split into three layers:

* **§2–3, derived phase facts.**  Parts (i) and (ii) of Liu–Wang's Lemma 4.1 are *theorems*
  here, and part (iii) is derived in the sharpened form `c/4 * ‖h‖² ≤ (S (p + h)).im`.
* **§6, quantitative remainder theorems.**  Explicit `ρ^(-1/2)` bounds with a computable
  constant.
* **§7, the leading convergence theorem.**  The statement `ρ^(d/2) ∫ e^{iρS} aρ → lead · Z_H`,
  stated and named separately from any rate.

## Main results

* `PhaseData.phase_apply_stationaryPoint`, `PhaseData.fderiv_phase_eq_zero`,
  `PhaseData.im_phase_ge` : Liu–Wang Lemma 4.1 (i), (ii), (iii), all **derived**.
* `oscIntegral_eq_integral_rescaled` : the exact rescaling identity — the normalization
  `ρ^(dim V / 2)` is precisely the Jacobian of `x = p + ρ^(-1/2) u`.
* `norm_rescaled_sub_le` : the pointwise majorant, uniform in `ρ`.
* `norm_oscIntegral_sub_amplitude_le`, `norm_oscIntegral_sub_lead_le` : the quantitative
  theorems.
* `oscIntegral_tendsto` : **the leading complex-Gaussian asymptotic**.
* `remainder_isBigO` : the `O(ρ^(-1/2))` rate.
* `gaussConst_phase_ne_zero`, `lead_eq_zero_of_tendsto_zero`,
  `eventually_oscIntegral_ne_zero` : coefficient recovery, with the non-vanishing of the
  leading constant **derived** from coercivity, not assumed.
-/
import LiuWang.LiuWang2025SemilinearWaveComplexAmplitudeFamily

noncomputable section

open MeasureTheory Complex Filter Set Asymptotics
open scoped Real Topology ENNReal NNReal

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

/-! ## 1.  Consequences of the phase hypotheses (Lemma 4.1 (i), (ii), (iii) are theorems) -/

namespace PhaseData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  (d : PhaseData V)

/-- **Liu–Wang Lemma 4.1 (i)**, derived: the phase vanishes at the interaction point. -/
theorem phase_apply_stationaryPoint : d.S d.p = 0 := by
  have h := d.taylor 0 (by simpa using d.hr.le)
  have h0 : ‖d.S d.p‖ ≤ 0 := by simpa using h
  exact norm_le_zero_iff.1 h0

lemma norm_hessian_le (h : V) : ‖d.H h h‖ ≤ ‖d.H‖ * ‖h‖ ^ 2 := by
  calc ‖d.H h h‖ ≤ ‖d.H h‖ * ‖h‖ := (d.H h).le_opNorm h
    _ ≤ (‖d.H‖ * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (d.H.le_opNorm h) (norm_nonneg h)
    _ = ‖d.H‖ * ‖h‖ ^ 2 := by ring

lemma norm_hessian_half_le (h : V) : ‖d.H h h / 2‖ ≤ ‖d.H‖ / 2 * ‖h‖ ^ 2 := by
  rw [norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have h3 := d.norm_hessian_le h
  linarith

/-- The phase is `O(‖h‖²)` on the localization ball. -/
theorem norm_phase_le {h : V} (hh : ‖h‖ ≤ d.r) :
    ‖d.S (d.p + h)‖ ≤ (‖d.H‖ / 2 + d.CR * d.r) * ‖h‖ ^ 2 := by
  have h1 := d.taylor h hh
  have h2 := d.norm_hessian_half_le h
  have h3 : ‖d.S (d.p + h)‖ ≤ ‖d.S (d.p + h) - d.H h h / 2‖ + ‖d.H h h / 2‖ := by
    simpa using norm_add_le (d.S (d.p + h) - d.H h h / 2) (d.H h h / 2)
  have h4 : d.CR * ‖h‖ ^ 3 ≤ d.CR * d.r * ‖h‖ ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖h‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg d.hCR hnn, hh, norm_nonneg h]
  linarith

/-- **Liu–Wang Lemma 4.1 (ii)**, derived: the phase is stationary at the interaction point. -/
theorem hasFDerivAt_phase : HasFDerivAt d.S (0 : V →L[ℝ] ℂ) d.p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [ContinuousLinearMap.zero_apply, sub_zero, d.phase_apply_stationaryPoint]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  set K : ℝ := ‖d.H‖ / 2 + d.CR * d.r with hK
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ d.CR * d.r := mul_nonneg d.hCR d.hr.le
    have h2 : (0 : ℝ) ≤ ‖d.H‖ / 2 := by positivity
    rw [hK]; linarith
  set δ : ℝ := min d.r (ε / (K + 1)) with hδ
  have hδ0 : 0 < δ := lt_min d.hr (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : V) hδ0] with h hh
  rw [mem_ball_zero_iff] at hh
  have hhr : ‖h‖ ≤ d.r := le_of_lt (lt_of_lt_of_le hh (min_le_left _ _))
  have hhδ : ‖h‖ ≤ ε / (K + 1) := le_of_lt (lt_of_lt_of_le hh (min_le_right _ _))
  have hmain := d.norm_phase_le hhr
  have hstep : K * ‖h‖ ≤ ε := by
    have h1 : K * ‖h‖ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hhδ hK0
    have h2 : K * (ε / (K + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0:ℝ) < K + 1)]
      nlinarith [hε.le, hK0]
    linarith
  calc ‖d.S (d.p + h)‖ ≤ K * ‖h‖ ^ 2 := hmain
    _ = (K * ‖h‖) * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hstep (norm_nonneg h)

/-- **Liu–Wang Lemma 4.1 (ii)**, in `fderiv` form. -/
theorem fderiv_phase_eq_zero : fderiv ℝ d.S d.p = 0 := d.hasFDerivAt_phase.fderiv

/-- **Liu–Wang Lemma 4.1 (iii)**, derived in sharp form on the localization ball:
the imaginary part of the phase is coercive with constant `c/4`. -/
theorem im_phase_ge {h : V} (hh : ‖h‖ ≤ d.r) :
    d.c / 4 * ‖h‖ ^ 2 ≤ (d.S (d.p + h)).im := by
  have h1 := d.taylor h hh
  have h2 : |(d.S (d.p + h) - d.H h h / 2).im| ≤ d.CR * ‖h‖ ^ 3 :=
    le_trans (Complex.abs_im_le_norm _) h1
  have h3 : d.c * ‖h‖ ^ 2 ≤ (d.H h h).im := d.coercive h
  have h4 : (d.S (d.p + h)).im
      = (d.S (d.p + h) - d.H h h / 2).im + (d.H h h).im / 2 := by
    rw [Complex.sub_im, half_im]; ring
  have h5 : d.CR * ‖h‖ ^ 3 ≤ d.c / 4 * ‖h‖ ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖h‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg d.hCR hnn, d.radiusSmall, hh, hnn, norm_nonneg h]
  have h6 := (abs_le.1 h2).1
  linarith

end PhaseData

/-! ## 2.  The oscillatory integral and its rescaling -/

section Osc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The integrand `exp (i ρ S x) · aρ x`. -/
def oscIntegrand (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (ρ : ℝ) (x : V) : ℂ :=
  Complex.exp (Complex.I * ρ * P.S x) * F.a ρ x

/-- The **normalized oscillatory integral** `ρ^(dim V / 2) ∫ exp (i ρ S x) aρ x dμ(x)`. -/
def oscIntegral (μ : Measure V) (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (ρ : ℝ) : ℂ :=
  (Real.sqrt ρ ^ Module.finrank ℝ V) • ∫ x, oscIntegrand P F ρ x ∂μ

/-- The rescaled integrand, i.e. the integrand read in the variable `u` with
`x = p + ρ^(-1/2) u`. -/
def rescaled (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (ρ : ℝ) (u : V) : ℂ :=
  oscIntegrand P F ρ (P.p + (Real.sqrt ρ)⁻¹ • u)

omit [FiniteDimensional ℝ V] in
lemma measurable_oscIntegrand (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (ρ : ℝ) :
    Measurable (oscIntegrand P F ρ) :=
  (Complex.continuous_exp.measurable.comp (measurable_const.mul P.measS)).mul (F.measurable ρ)

omit [FiniteDimensional ℝ V] in
lemma measurable_rescaled (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (ρ : ℝ) :
    Measurable (rescaled P F ρ) :=
  (measurable_oscIntegrand P F ρ).comp
    ((continuous_const.add (continuous_const_smul _)).measurable)

/-- **The rescaling identity.**  The normalization `ρ^(dim V / 2)` is exactly the Jacobian of
the substitution `x = p + ρ^(-1/2) u`, so the normalized oscillatory integral equals the
integral of the rescaled integrand with no leftover factor. -/
theorem oscIntegral_eq_integral_rescaled (μ : Measure V) [μ.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) {ρ : ℝ} (hρ : 0 < ρ) :
    oscIntegral μ P F ρ = ∫ u, rescaled P F ρ u ∂μ := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hstep : ∫ u, rescaled P F ρ u ∂μ
      = |((((Real.sqrt ρ)⁻¹) ^ Module.finrank ℝ V))⁻¹| • ∫ x, oscIntegrand P F ρ x ∂μ := by
    have h1 := Measure.integral_comp_smul (μ := μ)
      (fun y : V => oscIntegrand P F ρ (P.p + y)) ((Real.sqrt ρ)⁻¹)
    rw [show (fun u : V => rescaled P F ρ u)
        = fun u : V => (fun y : V => oscIntegrand P F ρ (P.p + y)) ((Real.sqrt ρ)⁻¹ • u) from rfl]
    rw [h1, integral_add_left_eq_self]
    rfl
  rw [hstep, oscIntegral]
  congr 1
  rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]

end Osc

/-! ## 3.  The pointwise majorant -/

section Bound

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The integrable majorant of the stationary-phase remainder.  Its terms are exactly the two
first-order corrections — the cubic jet of the phase (`‖u‖³`) and the first-order jet of the
amplitude (`‖u‖`) — plus the boundary tail (also absorbed into the `‖u‖` term).  It does not
depend on `ρ`. -/
def remainderBound (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (u : V) : ℝ :=
  (2 * F.A * P.CR * ‖u‖ ^ 3 + (F.L + F.A / P.r) * ‖u‖) *
    Real.exp (-(P.c / 4) * ‖u‖ ^ 2)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma quadratic_smul (H : V →L[ℝ] V →L[ℝ] ℂ) (t : ℝ) (u : V) :
    H (t • u) (t • u) = ((t * t : ℝ) : ℂ) * H u u := by
  -- Both slots are handled separately so that the real scalar is turned into a complex
  -- factor immediately, leaving no `ℝ`-action on `ℂ` in the goal.
  have hsnd : ∀ w : V, H w (t • u) = ((t : ℝ) : ℂ) * H w u := by
    intro w
    rw [map_smul]
    exact Complex.real_smul
  have hfst : H (t • u) u = ((t : ℝ) : ℂ) * H u u := by
    have h : H.flip u (t • u) = ((t : ℝ) : ℂ) * H.flip u u := by
      rw [map_smul]
      exact Complex.real_smul
    simp only [ContinuousLinearMap.flip_apply] at h
    exact h
  rw [hsnd (t • u), hfst]
  push_cast
  ring

variable (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Uniform Gaussian bound on the oscillatory factor over the localization ball. -/
lemma norm_exp_phase_le {ρ : ℝ} (hρ : 0 < ρ) {h : V} (hh : ‖h‖ ≤ P.r) :
    ‖Complex.exp (Complex.I * ρ * P.S (P.p + h))‖
      ≤ Real.exp (-(P.c / 4) * (ρ * ‖h‖ ^ 2)) := by
  rw [mul_assoc, norm_exp_I_mul]
  apply Real.exp_le_exp.2
  have h1 := P.im_phase_ge hh
  have h2 : ((ρ : ℂ) * P.S (P.p + h)).im = ρ * (P.S (P.p + h)).im := by
    simp [Complex.mul_im]
  rw [h2]
  linarith [mul_le_mul_of_nonneg_left h1 hρ.le]

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Uniform Gaussian bound on the whole rescaled integrand, uniform in `ρ`. -/
lemma norm_rescaled_le {ρ : ℝ} (hρ : 0 < ρ) (u : V) :
    ‖rescaled P F ρ u‖ ≤ F.A * Real.exp (-(P.c / 4) * ‖u‖ ^ 2) := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  set t : ℝ := (Real.sqrt ρ)⁻¹ with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htnorm : ‖t • u‖ = t * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hss : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
  have hrt2 : ρ * (t * t) = 1 := by
    rw [ht, ← mul_inv, hss]
    exact mul_inv_cancel₀ hρ.ne'
  have hsq : ρ * (t * ‖u‖) ^ 2 = ‖u‖ ^ 2 := by
    have hx : (t * ‖u‖) ^ 2 = (t * t) * ‖u‖ ^ 2 := by ring
    rw [hx, ← mul_assoc, hrt2, one_mul]
  by_cases hcase : ‖t • u‖ ≤ P.r
  · have h1 := norm_exp_phase_le P hρ hcase
    rw [rescaled, oscIntegrand, norm_mul]
    calc ‖Complex.exp (Complex.I * ρ * P.S (P.p + t • u))‖ * ‖F.a ρ (P.p + t • u)‖
        ≤ Real.exp (-(P.c / 4) * (ρ * ‖t • u‖ ^ 2)) * F.A :=
          mul_le_mul h1 (F.bound ρ _) (norm_nonneg _) (Real.exp_nonneg _)
      _ = F.A * Real.exp (-(P.c / 4) * ‖u‖ ^ 2) := by
          rw [htnorm, hsq]; ring
  · rw [not_le] at hcase
    have hz : F.a ρ (P.p + t • u) = 0 := F.supp ρ _ hcase
    rw [rescaled, oscIntegrand, hz, mul_zero, norm_zero]
    exact mul_nonneg F.hA (Real.exp_nonneg _)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **The pointwise majorant**, uniform in `ρ`.  This single estimate contains the whole
stationary-phase localization: the leading term is the amplitude *at the stationary point*
times the model Gaussian, and the error is `ρ^(-1/2)` times a fixed integrable function. -/
theorem norm_rescaled_sub_le {ρ : ℝ} (hρ : 0 < ρ) (u : V) :
    ‖rescaled P F ρ u - F.a ρ P.p * gaussKernel P.H u‖
      ≤ (Real.sqrt ρ)⁻¹ * remainderBound P F u := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  set t : ℝ := (Real.sqrt ρ)⁻¹ with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htnorm : ‖t • u‖ = t * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hss : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
  have hrt2 : ρ * (t * t) = 1 := by
    rw [ht, ← mul_inv, hss]
    exact mul_inv_cancel₀ hρ.ne'
  set E : ℝ := Real.exp (-(P.c / 4) * ‖u‖ ^ 2) with hE'
  have hE : (0 : ℝ) < E := Real.exp_pos _
  have hGn : ‖gaussKernel P.H u‖ ≤ Real.exp (-(P.c / 2) * ‖u‖ ^ 2) :=
    norm_gaussKernel_le P.coercive u
  have hexp4 : Real.exp (-(P.c / 2) * ‖u‖ ^ 2) ≤ E := by
    rw [hE']
    apply Real.exp_le_exp.2
    nlinarith [P.hc.le, sq_nonneg ‖u‖]
  have hGE : ‖gaussKernel P.H u‖ ≤ E := le_trans hGn hexp4
  have hrinv : (0 : ℝ) ≤ F.A / P.r := div_nonneg F.hA P.hr.le
  have hP1 : (0 : ℝ) ≤ t * (2 * F.A * P.CR * ‖u‖ ^ 3) * E := by
    refine mul_nonneg (mul_nonneg ht0.le ?_) hE.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) F.hA) P.hCR) (by positivity)
  have hP2 : (0 : ℝ) ≤ t * (F.L * ‖u‖) * E :=
    mul_nonneg (mul_nonneg ht0.le (mul_nonneg F.hL (norm_nonneg u))) hE.le
  have hP3 : (0 : ℝ) ≤ t * ((F.A / P.r) * ‖u‖) * E :=
    mul_nonneg (mul_nonneg ht0.le (mul_nonneg hrinv (norm_nonneg u))) hE.le
  have hsplitBound : t * remainderBound P F u
      = t * (2 * F.A * P.CR * ‖u‖ ^ 3) * E + t * (F.L * ‖u‖) * E
        + t * ((F.A / P.r) * ‖u‖) * E := by
    rw [remainderBound, hE']; ring
  by_cases hcase : ‖t • u‖ ≤ P.r
  · have hHs : P.H (t • u) (t • u) = ((t * t : ℝ) : ℂ) * P.H u u := quadratic_smul P.H t u
    set R : ℂ := P.S (P.p + t • u) - P.H (t • u) (t • u) / 2 with hR
    have hRn : ‖R‖ ≤ P.CR * ‖t • u‖ ^ 3 := P.taylor _ hcase
    set w : ℂ := Complex.I * ((ρ : ℂ) * R) with hw
    have hrc : ((ρ : ℝ) : ℂ) * ((t * t : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hrt2, Complex.ofReal_one]
    have hfac : Complex.exp (Complex.I * ρ * P.S (P.p + t • u))
        = gaussKernel P.H u * Complex.exp w := by
      rw [gaussKernel, ← Complex.exp_add, hw, hR, hHs]
      congr 1
      linear_combination (Complex.I * (P.H u u / 2)) * hrc
    have hwn : ‖w‖ ≤ P.CR * t * ‖u‖ ^ 3 := by
      rw [hw, norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ]
      calc ρ * ‖R‖ ≤ ρ * (P.CR * ‖t • u‖ ^ 3) := mul_le_mul_of_nonneg_left hRn hρ.le
        _ = P.CR * t * ‖u‖ ^ 3 := by
            rw [htnorm]
            have hx : ρ * (P.CR * (t * ‖u‖) ^ 3) = P.CR * (ρ * (t * t)) * t * ‖u‖ ^ 3 := by
              ring
            rw [hx, hrt2]; ring
    have hCRt : (0 : ℝ) ≤ P.CR * t * ‖u‖ ^ 3 :=
      mul_nonneg (mul_nonneg P.hCR ht0.le) (by positivity)
    have hsplit : rescaled P F ρ u - F.a ρ P.p * gaussKernel P.H u
        = gaussKernel P.H u * ((Complex.exp w - 1) * F.a ρ (P.p + t • u))
          + gaussKernel P.H u * (F.a ρ (P.p + t • u) - F.a ρ P.p) := by
      rw [rescaled, oscIntegrand, hfac]; ring
    have hT2 : ‖gaussKernel P.H u * (F.a ρ (P.p + t • u) - F.a ρ P.p)‖
        ≤ t * (F.L * ‖u‖) * E := by
      rw [norm_mul]
      have hlip : ‖F.a ρ (P.p + t • u) - F.a ρ P.p‖ ≤ F.L * (t * ‖u‖) := by
        have hx := F.lip ρ (P.p + t • u) P.p
        have hy : P.p + t • u - P.p = t • u := by abel
        rw [hy, htnorm] at hx
        exact hx
      calc ‖gaussKernel P.H u‖ * ‖F.a ρ (P.p + t • u) - F.a ρ P.p‖
          ≤ E * (F.L * (t * ‖u‖)) := mul_le_mul hGE hlip (norm_nonneg _) hE.le
        _ = t * (F.L * ‖u‖) * E := by ring
    have hkey : ‖gaussKernel P.H u‖ * ‖Complex.exp w - 1‖
        ≤ 2 * (P.CR * t * ‖u‖ ^ 3) * E := by
      by_cases hw1 : ‖w‖ ≤ 1
      · have h1 : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := Complex.norm_exp_sub_one_le hw1
        calc ‖gaussKernel P.H u‖ * ‖Complex.exp w - 1‖
            ≤ E * (2 * (P.CR * t * ‖u‖ ^ 3)) := by
              refine mul_le_mul hGE (le_trans h1 (by linarith)) (norm_nonneg _) hE.le
          _ = 2 * (P.CR * t * ‖u‖ ^ 3) * E := by ring
      · rw [not_le] at hw1
        have hGw : ‖gaussKernel P.H u * Complex.exp w‖ ≤ E := by
          rw [← hfac]
          have h1 := norm_exp_phase_le P hρ hcase
          have h2 : ρ * ‖t • u‖ ^ 2 = ‖u‖ ^ 2 := by
            rw [htnorm]
            have hx : (t * ‖u‖) ^ 2 = (t * t) * ‖u‖ ^ 2 := by ring
            rw [hx, ← mul_assoc, hrt2, one_mul]
          rw [h2] at h1
          exact h1
        have hone : (1 : ℝ) ≤ P.CR * t * ‖u‖ ^ 3 := le_trans hw1.le hwn
        have hdiff : ‖gaussKernel P.H u‖ * ‖Complex.exp w - 1‖ ≤ 2 * E := by
          have hx : ‖gaussKernel P.H u‖ * ‖Complex.exp w - 1‖
              = ‖gaussKernel P.H u * Complex.exp w - gaussKernel P.H u‖ := by
            rw [← norm_mul]; ring_nf
          rw [hx]
          calc ‖gaussKernel P.H u * Complex.exp w - gaussKernel P.H u‖
              ≤ ‖gaussKernel P.H u * Complex.exp w‖ + ‖gaussKernel P.H u‖ := norm_sub_le _ _
            _ ≤ E + E := add_le_add hGw hGE
            _ = 2 * E := by ring
        calc ‖gaussKernel P.H u‖ * ‖Complex.exp w - 1‖ ≤ 2 * E := hdiff
          _ = 2 * E * 1 := by ring
          _ ≤ 2 * E * (P.CR * t * ‖u‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hone (by positivity)
          _ = 2 * (P.CR * t * ‖u‖ ^ 3) * E := by ring
    have hT1 : ‖gaussKernel P.H u * ((Complex.exp w - 1) * F.a ρ (P.p + t • u))‖
        ≤ t * (2 * F.A * P.CR * ‖u‖ ^ 3) * E := by
      rw [norm_mul, norm_mul, ← mul_assoc]
      have hb : (0 : ℝ) ≤ 2 * (P.CR * t * ‖u‖ ^ 3) * E := mul_nonneg (by linarith) hE.le
      calc ‖gaussKernel P.H u‖ * ‖Complex.exp w - 1‖ * ‖F.a ρ (P.p + t • u)‖
          ≤ (2 * (P.CR * t * ‖u‖ ^ 3) * E) * F.A :=
            mul_le_mul hkey (F.bound ρ _) (norm_nonneg _) hb
        _ = t * (2 * F.A * P.CR * ‖u‖ ^ 3) * E := by ring
    rw [hsplit]
    calc ‖gaussKernel P.H u * ((Complex.exp w - 1) * F.a ρ (P.p + t • u))
            + gaussKernel P.H u * (F.a ρ (P.p + t • u) - F.a ρ P.p)‖
        ≤ ‖gaussKernel P.H u * ((Complex.exp w - 1) * F.a ρ (P.p + t • u))‖
            + ‖gaussKernel P.H u * (F.a ρ (P.p + t • u) - F.a ρ P.p)‖ := norm_add_le _ _
      _ ≤ t * (2 * F.A * P.CR * ‖u‖ ^ 3) * E + t * (F.L * ‖u‖) * E := add_le_add hT1 hT2
      _ ≤ t * remainderBound P F u := by rw [hsplitBound]; linarith
  · rw [not_le] at hcase
    have hz : F.a ρ (P.p + t • u) = 0 := F.supp ρ _ hcase
    have hres : rescaled P F ρ u = 0 := by rw [rescaled, oscIntegrand, hz, mul_zero]
    rw [hres, zero_sub, norm_neg, norm_mul]
    have hru : P.r < t * ‖u‖ := by rwa [htnorm] at hcase
    have hone : (1 : ℝ) ≤ (t * ‖u‖) / P.r := by rw [le_div_iff₀ P.hr]; linarith
    have hkey : ‖F.a ρ P.p‖ ≤ t * ((F.A / P.r) * ‖u‖) := by
      have hid : t * ((F.A / P.r) * ‖u‖) = F.A * ((t * ‖u‖) / P.r) := by field_simp
      rw [hid]
      exact le_trans (F.bound ρ P.p) (le_mul_of_one_le_right F.hA hone)
    calc ‖F.a ρ P.p‖ * ‖gaussKernel P.H u‖
        ≤ ‖F.a ρ P.p‖ * E := mul_le_mul_of_nonneg_left hGE (norm_nonneg _)
      _ ≤ t * ((F.A / P.r) * ‖u‖) * E := mul_le_mul_of_nonneg_right hkey hE.le
      _ ≤ t * remainderBound P F u := by rw [hsplitBound]; linarith

end Bound

/-! ## 4.  Integrability -/

section Integrability

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
  (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)

theorem integrable_remainderBound : Integrable (remainderBound P F) μ := by
  have h3 := integrable_pow_norm_mul_exp_neg_sq μ (α := P.c / 4) (by linarith [P.hc]) 3
  have h1 := integrable_pow_norm_mul_exp_neg_sq μ (α := P.c / 4) (by linarith [P.hc]) 1
  have hsum : Integrable (fun u : V =>
      (2 * F.A * P.CR) * (‖u‖ ^ 3 * Real.exp (-(P.c / 4) * ‖u‖ ^ 2))
        + (F.L + F.A / P.r) * (‖u‖ ^ 1 * Real.exp (-(P.c / 4) * ‖u‖ ^ 2))) μ :=
    (h3.const_mul _).add (h1.const_mul _)
  have heq : remainderBound P F = fun u : V =>
      (2 * F.A * P.CR) * (‖u‖ ^ 3 * Real.exp (-(P.c / 4) * ‖u‖ ^ 2))
        + (F.L + F.A / P.r) * (‖u‖ ^ 1 * Real.exp (-(P.c / 4) * ‖u‖ ^ 2)) := by
    funext u
    rw [remainderBound]
    ring
  rw [heq]
  exact hsum

theorem integrable_rescaled {ρ : ℝ} (hρ : 0 < ρ) : Integrable (rescaled P F ρ) μ := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_sq_norm μ (α := P.c / 4) (by linarith [P.hc])).const_mul F.A)
    (measurable_rescaled P F ρ).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun u => norm_rescaled_le P F hρ u)

/-- The oscillatory integrand itself is integrable — so `oscIntegral` is a genuine Bochner
integral, not a junk value.  (On the localization ball the imaginary part of the phase is
non-negative, so the oscillatory factor has modulus at most `1`; off the ball the amplitude
vanishes.) -/
theorem integrable_oscIntegrand {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (oscIntegrand P F ρ) μ := by
  have hcpt : IsCompact (Metric.closedBall P.p P.r) := isCompact_closedBall _ _
  have hfin : μ (Metric.closedBall P.p P.r) ≠ ⊤ := hcpt.measure_lt_top.ne
  have hball : Integrable ((Metric.closedBall P.p P.r).indicator (fun _ : V => F.A)) μ := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const hfin
  refine Integrable.mono' hball (measurable_oscIntegrand P F ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hxe : P.p + (x - P.p) = x := by abel
  by_cases hx : x ∈ Metric.closedBall P.p P.r
  · rw [Set.indicator_of_mem hx]
    have hxr : ‖x - P.p‖ ≤ P.r := by
      rwa [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [oscIntegrand, norm_mul]
    have h1 : ‖Complex.exp (Complex.I * ρ * P.S x)‖ ≤ 1 := by
      rw [← hxe, mul_assoc, norm_exp_I_mul, Real.exp_le_one_iff]
      have h2 : ((ρ : ℂ) * P.S (P.p + (x - P.p))).im = ρ * (P.S (P.p + (x - P.p))).im := by
        simp [Complex.mul_im]
      rw [h2]
      have h3 := P.im_phase_ge hxr
      have h4 : (0 : ℝ) ≤ P.c / 4 * ‖x - P.p‖ ^ 2 :=
        mul_nonneg (by linarith [P.hc]) (sq_nonneg _)
      have h5 : (0 : ℝ) ≤ (P.S (P.p + (x - P.p))).im := le_trans h4 h3
      nlinarith [h5, hρ.le]
    calc ‖Complex.exp (Complex.I * ρ * P.S x)‖ * ‖F.a ρ x‖
        ≤ 1 * F.A := mul_le_mul h1 (F.bound ρ x) (norm_nonneg _) zero_le_one
      _ = F.A := one_mul _
  · rw [Set.indicator_of_notMem hx]
    have hxr : P.r < ‖x - P.p‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      exact not_le.1 hx
    have hz : F.a ρ x = 0 := by rw [← hxe]; exact F.supp ρ _ hxr
    rw [oscIntegrand, hz, mul_zero, norm_zero]

end Integrability

/-! ## 5.  The complex-Gaussian leading constant is non-zero -/

section Const

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (P : PhaseData V)

/-- **The leading constant is non-zero**, derived from the `coercive` field alone via the
simultaneous diagonalization of `Re H` and `Im H`.  This is the constant `c ≠ 0` of (4.4). -/
theorem gaussConst_phase_ne_zero : gaussConst μ P.H ≠ 0 :=
  gaussConst_ne_zero μ P.hc P.coercive

end Const

/-! ## 6.  Quantitative remainder theorems -/

section Quantitative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
  (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)

/-- **Quantitative theorem I** (localization).  The normalized oscillatory integral is, up to
`O(ρ^(-1/2))`, the amplitude *at the stationary point and at the same `ρ`* times the model
complex-Gaussian constant.  No convergence hypothesis on the family is used. -/
theorem norm_oscIntegral_sub_amplitude_le {ρ : ℝ} (hρ : 0 < ρ) :
    ‖oscIntegral μ P F ρ - F.a ρ P.p * gaussConst μ P.H‖
      ≤ (Real.sqrt ρ)⁻¹ * ∫ u, remainderBound P F u ∂μ := by
  have hG : Integrable (gaussKernel P.H) μ := integrable_gaussKernel P.hc P.coercive
  have hR : Integrable (rescaled P F ρ) μ := integrable_rescaled μ P F hρ
  have hB : Integrable (remainderBound P F) μ := integrable_remainderBound μ P F
  have hconst : F.a ρ P.p * gaussConst μ P.H = ∫ u, F.a ρ P.p * gaussKernel P.H u ∂μ := by
    rw [gaussConst]
    exact (integral_const_mul _ _).symm
  rw [oscIntegral_eq_integral_rescaled μ P F hρ, hconst,
    ← integral_sub hR (hG.const_mul _)]
  calc ‖∫ u, (rescaled P F ρ u - F.a ρ P.p * gaussKernel P.H u) ∂μ‖
      ≤ ∫ u, ‖rescaled P F ρ u - F.a ρ P.p * gaussKernel P.H u‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u, (Real.sqrt ρ)⁻¹ * remainderBound P F u ∂μ := by
        refine integral_mono ((hR.sub (hG.const_mul _)).norm) (hB.const_mul _) ?_
        intro u
        exact norm_rescaled_sub_le P F hρ u
    _ = (Real.sqrt ρ)⁻¹ * ∫ u, remainderBound P F u ∂μ := integral_const_mul _ _

/-- **Quantitative theorem II** (localization + amplitude convergence).  The error relative to
the *limiting* leading coefficient splits into the `O(ρ^(-1/2))` stationary-phase error and the
amplitude's own modulus of convergence. -/
theorem norm_oscIntegral_sub_lead_le {ρ : ℝ} (hρ : 0 < ρ) :
    ‖oscIntegral μ P F ρ - F.lead * gaussConst μ P.H‖
      ≤ (Real.sqrt ρ)⁻¹ * (∫ u, remainderBound P F u ∂μ)
        + ‖F.a ρ P.p - F.lead‖ * ‖gaussConst μ P.H‖ := by
  have hsplit : oscIntegral μ P F ρ - F.lead * gaussConst μ P.H
      = (oscIntegral μ P F ρ - F.a ρ P.p * gaussConst μ P.H)
        + (F.a ρ P.p - F.lead) * gaussConst μ P.H := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact norm_oscIntegral_sub_amplitude_le μ P F hρ
  · rw [norm_mul]

lemma tendsto_inv_sqrt_atTop : Tendsto (fun ρ : ℝ => (Real.sqrt ρ)⁻¹) atTop (𝓝 0) :=
  Filter.Tendsto.inv_tendsto_atTop Real.tendsto_sqrt_atTop

/-- **The `O(ρ^(-1/2))` rate**, relative to the same-`ρ` amplitude value.  This is the
strongest rate the hypotheses support; see the README for the additional jet cancellations
that would upgrade it. -/
theorem remainder_isBigO :
    (fun ρ : ℝ => oscIntegral μ P F ρ - F.a ρ P.p * gaussConst μ P.H)
      =O[atTop] (fun ρ : ℝ => (Real.sqrt ρ)⁻¹) := by
  refine Asymptotics.IsBigO.of_bound (∫ u, remainderBound P F u ∂μ) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have := norm_oscIntegral_sub_amplitude_le μ P F hρ
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt ρ)⁻¹)]
  linarith [this]

end Quantitative

/-! ## 7.  The leading convergence theorem -/

section Leading

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
  (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)

/-- **The leading complex-Gaussian asymptotic for a ρ-dependent amplitude family.**

`ρ^(dim V / 2) ∫ exp (i ρ S x) · aρ x  dμ(x)  →  lead · ∫ exp (i H(u,u)/2) dμ(u)`

as `ρ → ∞`.  The right-hand constant is non-zero by `gaussConst_phase_ne_zero`.

This statement carries no rate; the rates are the separate theorems of §6. -/
theorem oscIntegral_tendsto :
    Tendsto (fun ρ : ℝ => oscIntegral μ P F ρ) atTop (𝓝 (F.lead * gaussConst μ P.H)) := by
  rw [← sub_zero (F.lead * gaussConst μ P.H)]
  have hgoal : Tendsto
      (fun ρ : ℝ => oscIntegral μ P F ρ - F.lead * gaussConst μ P.H) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (g := fun ρ : ℝ => (Real.sqrt ρ)⁻¹ * (∫ u, remainderBound P F u ∂μ)
        + ‖F.a ρ P.p - F.lead‖ * ‖gaussConst μ P.H‖)
      (Filter.Eventually.of_forall fun ρ => norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
      exact norm_oscIntegral_sub_lead_le μ P F hρ
    · have h1 : Tendsto (fun ρ : ℝ => (Real.sqrt ρ)⁻¹ * (∫ u, remainderBound P F u ∂μ))
          atTop (𝓝 0) := by
        simpa using tendsto_inv_sqrt_atTop.mul_const (∫ u, remainderBound P F u ∂μ)
      have h2 : Tendsto (fun ρ : ℝ => ‖F.a ρ P.p - F.lead‖ * ‖gaussConst μ P.H‖)
          atTop (𝓝 0) := by
        have hd : Tendsto (fun ρ : ℝ => F.a ρ P.p - F.lead) atTop (𝓝 0) := by
          simpa using F.tendsto_lead.sub_const F.lead
        simpa using hd.norm.mul_const ‖gaussConst μ P.H‖
      simpa using h1.add h2
  have := hgoal.add_const (F.lead * gaussConst μ P.H)
  simpa using this

/-! ## 8.  Coefficient recovery -/

/-- **Coefficient recovery, vanishing form.**  If the normalized oscillatory integral tends to
`0`, then the *limiting* leading amplitude vanishes.  No non-degeneracy side condition is
needed: the non-vanishing of the complex-Gaussian constant is derived from `P.coercive`. -/
theorem lead_eq_zero_of_tendsto_zero
    (h0 : Tendsto (fun ρ : ℝ => oscIntegral μ P F ρ) atTop (𝓝 0)) : F.lead = 0 := by
  have h1 := oscIntegral_tendsto μ P F
  have h2 : F.lead * gaussConst μ P.H = 0 := tendsto_nhds_unique h1 h0
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exact absurd h (gaussConst_phase_ne_zero μ P)

/-- **Coefficient recovery, quantitative form.** -/
theorem eventually_norm_oscIntegral_ge (ha : F.lead ≠ 0) :
    ∀ᶠ ρ in atTop, ‖F.lead * gaussConst μ P.H‖ / 2 ≤ ‖oscIntegral μ P F ρ‖ := by
  have hpos : 0 < ‖F.lead * gaussConst μ P.H‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero ha (gaussConst_phase_ne_zero μ P)
  have hn : Tendsto (fun ρ : ℝ => ‖oscIntegral μ P F ρ‖) atTop
      (𝓝 ‖F.lead * gaussConst μ P.H‖) := (oscIntegral_tendsto μ P F).norm
  filter_upwards [hn.eventually (eventually_gt_nhds
    (by linarith : ‖F.lead * gaussConst μ P.H‖ / 2 < ‖F.lead * gaussConst μ P.H‖))] with ρ hρ
  exact hρ.le

/-- **Coefficient recovery, eventual non-vanishing.** -/
theorem eventually_oscIntegral_ne_zero (ha : F.lead ≠ 0) :
    ∀ᶠ ρ in atTop, oscIntegral μ P F ρ ≠ 0 := by
  have hpos : 0 < ‖F.lead * gaussConst μ P.H‖ := by
    rw [norm_pos_iff]; exact mul_ne_zero ha (gaussConst_phase_ne_zero μ P)
  filter_upwards [eventually_norm_oscIntegral_ge μ P F ha] with ρ hρ
  intro h
  rw [h, norm_zero] at hρ
  linarith

end Leading

end LiuWang2025SemilinearWaveComplexStationaryPhase
