/-
Copyright (c) 2026.  Released under Apache 2.0.

# Complex Gaussian normal form

This file develops the *model* complex Gaussian
`gaussKernel H u = exp (I * (H u u / 2))`
attached to a continuous complex bilinear form `H` on a finite-dimensional real normed
space `V` whose imaginary part is coercive:

`c * ‖u‖ ^ 2 ≤ (H u u).im`  with  `0 < c`.

It is the first half of a self-contained formalization of the **analytic localization step**
behind equation (4.4) of

  B. Liu and W. Wang, *On a partial data inverse problem for the semi-linear wave equation*,
  arXiv:2511.08794v1, Section 4.2,

where the phase `S = κ₀φ⁽⁰⁾ + κ₁φ⁽¹⁾ + κ₂φ⁽²⁾ + κ₃φ⁽³⁾` satisfies the hypotheses of their
Lemma 4.1 at the interaction point `p̃`.

Nothing in this file refers to the wave equation, the Dirichlet-to-Neumann map, Gaussian beams
or higher-order linearization: the content is pure finite-dimensional complex stationary phase.

## Main results

* `integrable_pow_norm_mul_exp_neg_sq` : on any finite-dimensional real normed space carrying an
  additive Haar measure, `‖u‖ ^ k * exp (-α * ‖u‖ ^ 2)` is integrable for `0 < α`.
  (Reusable; no paper-specific constants.)
* `integrable_gaussKernel` : the model complex Gaussian is integrable.
* `gaussConst` : its integral, the leading constant of the stationary-phase expansion.
* `gaussConst_diagForm` : closed form of `gaussConst` for a diagonal `H`, via Mathlib's
  multidimensional complex Gaussian integral.
* `gaussConst_diagForm_ne_zero` : the leading constant is non-zero in the diagonal case.
* `gaussConst_ne_zero_of_diagonalizing_equiv` : the leading constant is non-zero whenever `H`
  becomes diagonal after a real linear change of variables (Haar-uniqueness transfer).
* `exists_orthoBasis_of_coercive` : **simultaneous diagonalization** — coercivity of `Im H`
  alone produces a basis of `V` orthogonal for the symmetrized form of `H`.
* `gaussConst_ne_zero` : **the leading constant is non-zero for every coercive `H`**, with
  respect to every additive Haar measure on every finite-dimensional real normed space.
-/
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open MeasureTheory Complex Filter Set
open scoped Real Topology ENNReal NNReal RealInnerProductSpace

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

/-! ## 1.  Elementary complex arithmetic -/

lemma half_im (z : ℂ) : (z / 2).im = z.im / 2 := by simp

lemma half_re (z : ℂ) : (z / 2).re = z.re / 2 := by simp

/-- `‖exp (I * z)‖ = exp (-z.im)`.  This is the only place where the oscillatory factor is
converted into a real Gaussian weight. -/
lemma norm_exp_I_mul (z : ℂ) : ‖Complex.exp (Complex.I * z)‖ = Real.exp (-z.im) := by
  rw [Complex.norm_exp, Complex.I_mul_re]

/-! ## 2.  The complex Gaussian kernel -/

section Kernel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The model complex Gaussian `exp (i H(u,u)/2)` attached to the complex quadratic form
`u ↦ H u u`.  In the application `H` is the complex Hessian of the phase at the stationary
point. -/
def gaussKernel (H : V →L[ℝ] V →L[ℝ] ℂ) (u : V) : ℂ :=
  Complex.exp (Complex.I * (H u u / 2))

lemma continuous_quadratic (H : V →L[ℝ] V →L[ℝ] ℂ) : Continuous fun u => H u u := by
  have hpair : Continuous fun u : V => (u, u) := by fun_prop
  exact H.continuous₂.comp hpair

lemma continuous_gaussKernel (H : V →L[ℝ] V →L[ℝ] ℂ) : Continuous (gaussKernel H) :=
  Complex.continuous_exp.comp (continuous_const.mul ((continuous_quadratic H).div_const 2))

lemma measurable_gaussKernel {_ : MeasurableSpace V} [OpensMeasurableSpace V] [BorelSpace V]
    (H : V →L[ℝ] V →L[ℝ] ℂ) : Measurable (gaussKernel H) :=
  (continuous_gaussKernel H).measurable

/-- The modulus of the model Gaussian is a real Gaussian governed by `Im H`. -/
lemma norm_gaussKernel (H : V →L[ℝ] V →L[ℝ] ℂ) (u : V) :
    ‖gaussKernel H u‖ = Real.exp (-((H u u).im / 2)) := by
  rw [gaussKernel, norm_exp_I_mul, half_im]

/-- **The model Gaussian is even.**  Together with `integral_eq_zero_of_odd` this is the
parity cancellation that upgrades the stationary-phase rate from `O(ρ^(-1/2))` to `O(ρ^(-1))`
once the cubic jet of the phase and the first-order jet of the amplitude are available; see
the README, §6.2. -/
@[simp] lemma gaussKernel_neg (H : V →L[ℝ] V →L[ℝ] ℂ) (u : V) :
    gaussKernel H (-u) = gaussKernel H u := by
  have h : H (-u) (-u) = H u u := by simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [gaussKernel, gaussKernel, h]

/-- Coercivity of `Im H` turns the model Gaussian into a genuinely decaying weight. -/
lemma norm_gaussKernel_le {H : V →L[ℝ] V →L[ℝ] ℂ} {c : ℝ}
    (hH : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).im) (u : V) :
    ‖gaussKernel H u‖ ≤ Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
  rw [norm_gaussKernel]
  apply Real.exp_le_exp.2
  have h := hH u
  linarith

end Kernel

/-! ## 3.  A reusable finite-dimensional integrability lemma -/

section Integrability

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

/-- **Polynomial × Gaussian is Haar-integrable in finite dimensions.**

On any finite-dimensional real normed space with an additive Haar measure, the function
`u ↦ ‖u‖ ^ k * exp (-α ‖u‖ ^ 2)` is integrable for every `k : ℕ` and every `α > 0`.
This is the only integrability input of the whole development, and it involves no constants
specific to the Liu–Wang setting. -/
theorem integrable_pow_norm_mul_exp_neg_sq {α : ℝ} (hα : 0 < α) (k : ℕ) :
    Integrable (fun u : V => ‖u‖ ^ k * Real.exp (-α * ‖u‖ ^ 2)) μ := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- A zero-dimensional space: `μ` is finite and the integrand is constant.
    have huniv : (Set.univ : Set V) = {(0 : V)} := by
      ext x; simp [Subsingleton.elim x (0 : V)]
    have hfin : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      rw [huniv]
      exact (isCompact_singleton (x := (0 : V))).measure_lt_top
    have : (fun u : V => ‖u‖ ^ k * Real.exp (-α * ‖u‖ ^ 2))
        = fun _ : V => ‖(0 : V)‖ ^ k * Real.exp (-α * ‖(0 : V)‖ ^ 2) := by
      funext u; rw [Subsingleton.elim u (0 : V)]
    rw [this]
    exact integrable_const _
  · -- Positive dimension: reduce to a radial integral and quote the one-dimensional
    -- `polynomial × Gaussian` result.
    refine (integrable_fun_norm_addHaar μ
      (f := fun y : ℝ => y ^ k * Real.exp (-α * y ^ 2))).2 ?_
    have hrw : (fun y : ℝ => y ^ (Module.finrank ℝ V - 1) •
          ((fun y : ℝ => y ^ k * Real.exp (-α * y ^ 2)) y))
        = fun y : ℝ => y ^ (Module.finrank ℝ V - 1 + k) * Real.exp (-α * y ^ 2) := by
      funext y
      simp only [smul_eq_mul, pow_add]
      ring
    rw [hrw]
    have hs : (-1 : ℝ) < ((Module.finrank ℝ V - 1 + k : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((Module.finrank ℝ V - 1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h1 := integrableOn_rpow_mul_exp_neg_mul_sq (b := α) hα hs
    simpa only [Real.rpow_natCast] using h1

/-- The pure Gaussian case `k = 0`. -/
theorem integrable_exp_neg_mul_sq_norm {α : ℝ} (hα : 0 < α) :
    Integrable (fun u : V => Real.exp (-α * ‖u‖ ^ 2)) μ := by
  simpa using integrable_pow_norm_mul_exp_neg_sq μ hα 0

variable {μ}

/-- The model complex Gaussian is integrable as soon as `Im H` is coercive. -/
theorem integrable_gaussKernel {H : V →L[ℝ] V →L[ℝ] ℂ} {c : ℝ} (hc : 0 < c)
    (hH : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).im) : Integrable (gaussKernel H) μ := by
  refine Integrable.mono' (integrable_exp_neg_mul_sq_norm μ (α := c / 2) (by linarith))
    (continuous_gaussKernel H).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun u => norm_gaussKernel_le hH u)

end Integrability

/-! ## 4.  The leading constant -/

section Const

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The leading constant of the complex stationary-phase expansion: the integral of the
model complex Gaussian.  This is the `c` of equation (4.4) of Liu–Wang. -/
def gaussConst (μ : Measure V) (H : V →L[ℝ] V →L[ℝ] ℂ) : ℂ := ∫ u, gaussKernel H u ∂μ

/-- **Parity cancellation.**  An odd function has vanishing integral against any additive
Haar measure.  This is the exact ingredient that makes the `ρ^(-1/2)` coefficient of the
stationary-phase expansion vanish under the additional jet hypotheses described in the
README, §6.2. -/
theorem integral_eq_zero_of_odd (μ : Measure V) [μ.IsAddHaarMeasure] {f : V → ℂ}
    (hodd : ∀ u : V, f (-u) = -f u) : ∫ u, f u ∂μ = 0 := by
  have h1 : ∫ u, f (-u) ∂μ = ∫ u, f u ∂μ := integral_neg_eq_self f μ
  have h2 : ∫ u, f (-u) ∂μ = -∫ u, f u ∂μ := by
    simp only [hodd, integral_neg]
  have h3 : (2 : ℂ) * ∫ u, f u ∂μ = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← h1, h2]
    ring
  exact (mul_eq_zero.1 h3).resolve_left two_ne_zero

end Const

/-! ## 5.  Diagonal quadratic forms and non-vanishing of the leading constant -/

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- The diagonal complex quadratic form `u ↦ ∑ i, m i * (u i) ^ 2` on `ι → ℝ`, as a continuous
bilinear map. -/
def diagForm (m : ι → ℂ) : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ :=
  ∑ i : ι, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).smulRight
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).smulRight (m i))

lemma diagForm_apply (m : ι → ℂ) (u v : ι → ℝ) :
    diagForm m u v = ∑ i : ι, ((u i * v i : ℝ) : ℂ) * m i := by
  simp only [diagForm, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  exact Complex.real_smul

lemma diagForm_self (m : ι → ℂ) (u : ι → ℝ) :
    diagForm m u u = ∑ i : ι, m i * ((u i : ℂ)) ^ 2 := by
  rw [diagForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

lemma diagForm_self_im (m : ι → ℂ) (u : ι → ℝ) :
    (diagForm m u u).im = ∑ i : ι, (m i).im * (u i) ^ 2 := by
  rw [diagForm_self, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_im, pow_two, Complex.mul_re]
  try ring

/-- The Gaussian exponent used by Mathlib's multidimensional complex Gaussian integral:
`exp (I * (∑ m i uᵢ²)/2) = exp (-∑ (gaussB m i) uᵢ²)`. -/
def gaussB (m : ι → ℂ) (i : ι) : ℂ := -(Complex.I * m i / 2)

omit [Fintype ι] in
lemma gaussB_re (m : ι → ℂ) (i : ι) : (gaussB m i).re = (m i).im / 2 := by
  simp only [gaussB, Complex.neg_re, half_re, Complex.I_mul_re]
  ring

omit [Fintype ι] in
lemma gaussB_ne_zero {m : ι → ℂ} (hm : ∀ i, 0 < (m i).im) (i : ι) : gaussB m i ≠ 0 := by
  intro h
  have hre := gaussB_re m i
  rw [h] at hre
  simp only [Complex.zero_re] at hre
  have hpos := hm i
  linarith

/-- Closed form for the leading constant of a diagonal complex quadratic form.

This is Mathlib's multidimensional complex Gaussian integral
(`GaussianFourier.integral_cexp_neg_sum_mul_add`) transported to the normalization used
here. -/
theorem gaussConst_diagForm {m : ι → ℂ} (hm : ∀ i, 0 < (m i).im) :
    gaussConst (volume : Measure (ι → ℝ)) (diagForm m)
      = ∏ i : ι, (↑π / gaussB m i) ^ (1 / 2 : ℂ) := by
  have hb : ∀ i, 0 < (gaussB m i).re := by
    intro i; rw [gaussB_re]; have h := hm i; linarith
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add (b := gaussB m) hb (fun _ => 0)
  have hexp : ∀ v : ι → ℝ,
      Complex.exp (-∑ i : ι, gaussB m i * (v i : ℂ) ^ 2 + ∑ i : ι, (0 : ℂ) * (v i : ℂ))
        = gaussKernel (diagForm m) v := by
    intro v
    rw [gaussKernel, diagForm_self]
    congr 1
    simp only [zero_mul, Finset.sum_const_zero, add_zero, gaussB, Finset.sum_div,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hexp] at key
  rw [gaussConst, key]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- **Non-vanishing of the leading constant, diagonal case.** -/
theorem gaussConst_diagForm_ne_zero {m : ι → ℂ} (hm : ∀ i, 0 < (m i).im) :
    gaussConst (volume : Measure (ι → ℝ)) (diagForm m) ≠ 0 := by
  rw [gaussConst_diagForm hm]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Ne, Complex.cpow_eq_zero_iff]
  rintro ⟨h, -⟩
  have hb : gaussB m i ≠ 0 := gaussB_ne_zero hm i
  have hpi : (π : ℂ) ≠ 0 := by simp
  simp [div_eq_zero_iff, hb, hpi] at h

end Diagonal

/-! ## 6.  Transfer of non-vanishing along a linear change of variables -/

section Transfer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Two additive Haar measures give proportional integrals**, with a strictly positive
proportionality constant.  A convenient packaging of Haar uniqueness. -/
theorem exists_pos_integral_eq_of_isAddHaarMeasure
    (μ' μ : Measure V) [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] (f : V → ℂ) :
    ∃ k : ℝ, 0 < k ∧ ∫ v, f v ∂μ' = (k : ℂ) * ∫ v, f v ∂μ := by
  refine ⟨(Measure.addHaarScalarFactor μ' μ : ℝ≥0), ?_, ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ
  · have hμ' : μ' = (Measure.addHaarScalarFactor μ' μ : ℝ≥0) • μ :=
      Measure.isAddLeftInvariant_eq_smul μ' μ
    conv_lhs => rw [hμ']
    rw [MeasureTheory.integral_smul_nnreal_measure, NNReal.smul_def]
    exact Complex.real_smul

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **Non-vanishing of the leading constant for any `H` that is diagonalizable by a real
linear change of variables.**

If a real linear homeomorphism `T : (ι → ℝ) ≃L[ℝ] V` puts `H` in the diagonal normal form
`H (T u) (T u) = ∑ i, m i * (u i) ^ 2` with `0 < (m i).im`, then the leading constant of `H`
with respect to *any* additive Haar measure on `V` is non-zero. -/
theorem gaussConst_ne_zero_of_diagonalizing_equiv
    {ι : Type*} [Fintype ι] (μ : Measure V) [μ.IsAddHaarMeasure]
    {H : V →L[ℝ] V →L[ℝ] ℂ} (T : (ι → ℝ) ≃L[ℝ] V) (m : ι → ℂ)
    (hm : ∀ i, 0 < (m i).im)
    (hT : ∀ u : ι → ℝ, H (T u) (T u) = ∑ i : ι, m i * ((u i : ℂ)) ^ 2) :
    gaussConst μ H ≠ 0 := by
  have hmap : ∫ v, gaussKernel H v ∂((volume : Measure (ι → ℝ)).map T)
      = ∫ u : ι → ℝ, gaussKernel H (T u) :=
    integral_map_of_stronglyMeasurable T.continuous.measurable
      (continuous_gaussKernel H).stronglyMeasurable
  have hdiag : ∀ u : ι → ℝ, gaussKernel H (T u) = gaussKernel (diagForm m) u := by
    intro u
    rw [gaussKernel, gaussKernel, hT u, diagForm_self]
  have hne : ∫ v, gaussKernel H v ∂((volume : Measure (ι → ℝ)).map T) ≠ 0 := by
    rw [hmap]
    simp only [hdiag]
    exact gaussConst_diagForm_ne_zero hm
  obtain ⟨k, hk, hkeq⟩ := exists_pos_integral_eq_of_isAddHaarMeasure
    ((volume : Measure (ι → ℝ)).map T) μ (fun v => gaussKernel H v)
  intro hzero
  rw [gaussConst] at hzero
  rw [hkeq, hzero, mul_zero] at hne
  exact hne rfl

end Transfer



/-! ## 7.  Orthogonal bases and the diagonal normal form -/

section OrthoBasis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If a basis is orthogonal for the symmetrized form of `H`, then the quadratic form
`u ↦ H u u` is diagonal in the corresponding coordinates. -/
theorem quadratic_eq_sum_of_ortho {H : V →L[ℝ] V →L[ℝ] ℂ} {n : ℕ} (b : Module.Basis (Fin n) ℝ V)
    (hb : ∀ i j, i ≠ j → H (b i) (b j) + H (b j) (b i) = 0) (x : Fin n → ℝ) :
    H (∑ i, x i • b i) (∑ i, x i • b i) = ∑ i, H (b i) (b i) * ((x i : ℂ)) ^ 2 := by
  set F : Fin n → Fin n → ℂ := fun i j => ((x i * x j : ℝ) : ℂ) * H (b i) (b j) with hF
  -- Linearity of a continuous linear functional along the basis expansion.  Stated as a
  -- separate `have` so that the real scalar is converted to a complex factor *before* any
  -- `ℝ`-action on `ℂ` is left in the goal.
  have hlin : ∀ (K : V →L[ℝ] ℂ) (y : Fin n → ℝ),
      K (∑ j, y j • b j) = ∑ j, ((y j : ℝ) : ℂ) * K (b j) := by
    intro K y
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    exact Complex.real_smul
  have hexp : H (∑ i, x i • b i) (∑ i, x i • b i) = ∑ i, ∑ j, F i j := by
    have hfl : H (∑ i, x i • b i) (∑ i, x i • b i)
        = ∑ i, ((x i : ℝ) : ℂ) * H (b i) (∑ j, x j • b j) := by
      have h := hlin (H.flip (∑ j, x j • b j)) x
      simp only [ContinuousLinearMap.flip_apply] at h
      exact h
    rw [hfl, hF]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlin (H (b i)) x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hoff : ∀ i j, i ≠ j → F i j + F j i = 0 := by
    intro i j hij
    have h := hb i j hij
    rw [hF]
    simp only
    have hc : ((x j * x i : ℝ) : ℂ) = ((x i * x j : ℝ) : ℂ) := by push_cast; ring
    rw [hc, ← mul_add, h, mul_zero]
  have hrow : ∀ i, ∑ j, (F i j + F j i) = F i i + F i i := by
    intro i
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      exact hoff i j (Ne.symm hji)
    · intro h; exact absurd (Finset.mem_univ i) h
  have hdouble : ∑ i, ∑ j, (F i j + F j i) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F i j) := by
    have e1 : ∑ i, ∑ j, (F i j + F j i) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F j i) := by
      simp_rw [Finset.sum_add_distrib]
    rw [e1]
    congr 1
    exact Finset.sum_comm
  have hkey : (∑ i, ∑ j, F i j) = ∑ i, F i i := by
    have h1 : ∑ i, ∑ j, (F i j + F j i) = ∑ i, (F i i + F i i) :=
      Finset.sum_congr rfl fun i _ => hrow i
    rw [hdouble, Finset.sum_add_distrib] at h1
    have h3 : (2 : ℂ) * (∑ i, ∑ j, F i j) = 2 * ∑ i, F i i := by
      rw [two_mul, two_mul]; exact h1
    exact mul_left_cancel₀ two_ne_zero h3
  rw [hexp, hkey, hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only
  push_cast
  ring

/-- **Non-vanishing of the leading constant from an orthogonal basis.**
If some basis of `V` is orthogonal for the symmetrized form of `H`, then the leading constant
of the complex Gaussian attached to `H` is non-zero. -/
theorem gaussConst_ne_zero_of_orthoBasis (μ : Measure V) [μ.IsAddHaarMeasure]
    {H : V →L[ℝ] V →L[ℝ] ℂ} {c : ℝ} (hc : 0 < c)
    (hH : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).im)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V)
    (hb : ∀ i j, i ≠ j → H (b i) (b j) + H (b j) (b i) = 0) :
    gaussConst μ H ≠ 0 := by
  refine gaussConst_ne_zero_of_diagonalizing_equiv μ
    (b.equivFun.symm.toContinuousLinearEquiv) (fun i => H (b i) (b i)) ?_ ?_
  · intro i
    have hbi : (0 : ℝ) < ‖b i‖ := norm_pos_iff.2 (b.ne_zero i)
    have h := hH (b i)
    have hpos : 0 < c * ‖b i‖ ^ 2 := mul_pos hc (pow_pos hbi 2)
    linarith
  · intro u
    have hcoe : (b.equivFun.symm.toContinuousLinearEquiv) u = ∑ i, u i • b i := by
      simp [Module.Basis.equivFun_symm_apply]
    rw [hcoe, quadratic_eq_sum_of_ortho b hb u]

end OrthoBasis



/-! ## 8.  Real and imaginary parts of the symmetrized form -/

section Forms

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The symmetrization `H u v + H v u` of a continuous complex bilinear form. -/
def symCLM (H : V →L[ℝ] V →L[ℝ] ℂ) : V →L[ℝ] V →L[ℝ] ℂ := H + H.flip

lemma symCLM_apply (H : V →L[ℝ] V →L[ℝ] ℂ) (u v : V) :
    symCLM H u v = H u v + H v u := by
  simp [symCLM]

lemma symCLM_comm (H : V →L[ℝ] V →L[ℝ] ℂ) (u v : V) : symCLM H u v = symCLM H v u := by
  rw [symCLM_apply, symCLM_apply, add_comm]

/-- A real bilinear form obtained from a continuous complex bilinear form by postcomposing
with a real-linear functional on `ℂ` (in practice `Complex.reLm` or `Complex.imLm`). -/
def bilinComp (H : V →L[ℝ] V →L[ℝ] ℂ) (φ : ℂ →ₗ[ℝ] ℝ) : LinearMap.BilinForm ℝ V where
  toFun u := φ.comp (H u).toLinearMap
  map_add' u v := by ext w; simp
  map_smul' c u := by
    ext w
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    rw [map_smul H c u, ContinuousLinearMap.smul_apply, map_smul φ, smul_eq_mul]

@[simp] lemma bilinComp_apply (H : V →L[ℝ] V →L[ℝ] ℂ) (φ : ℂ →ₗ[ℝ] ℝ) (u v : V) :
    bilinComp H φ u v = φ (H u v) := rfl

end Forms



/-! ## 9.  Simultaneous diagonalization -/

section Diagonalize

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Expansion of a real bilinear form on linear combinations of an orthogonal family. -/
lemma bilin_orthogonal_sum (B : LinearMap.BilinForm ℝ V) {n : ℕ} (g : Fin n → V)
    (horth : ∀ i j, i ≠ j → B (g i) (g j) = 0) (x y : Fin n → ℝ) :
    B (∑ i, x i • g i) (∑ j, y j • g j) = ∑ i, (x i * y i) * B (g i) (g i) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [horth j i hji, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The imaginary part of the symmetrized form, as a real bilinear form. -/
def imForm (H : V →L[ℝ] V →L[ℝ] ℂ) : LinearMap.BilinForm ℝ V :=
  bilinComp (symCLM H) Complex.imLm

/-- The real part of the symmetrized form, as a real bilinear form. -/
def reForm (H : V →L[ℝ] V →L[ℝ] ℂ) : LinearMap.BilinForm ℝ V :=
  bilinComp (symCLM H) Complex.reLm

lemma imForm_apply (H : V →L[ℝ] V →L[ℝ] ℂ) (u v : V) :
    imForm H u v = (H u v + H v u).im := by
  simp [imForm, symCLM_apply, Complex.imLm]

lemma reForm_apply (H : V →L[ℝ] V →L[ℝ] ℂ) (u v : V) :
    reForm H u v = (H u v + H v u).re := by
  simp [reForm, symCLM_apply, Complex.reLm]

lemma imForm_comm (H : V →L[ℝ] V →L[ℝ] ℂ) (u v : V) : imForm H u v = imForm H v u := by
  rw [imForm_apply, imForm_apply, add_comm]

lemma reForm_comm (H : V →L[ℝ] V →L[ℝ] ℂ) (u v : V) : reForm H u v = reForm H v u := by
  rw [reForm_apply, reForm_apply, add_comm]

lemma imForm_self (H : V →L[ℝ] V →L[ℝ] ℂ) (u : V) : imForm H u u = 2 * (H u u).im := by
  rw [imForm_apply]
  simp [Complex.add_im]
  ring

lemma isSymm_of_comm {B : LinearMap.BilinForm ℝ V} (h : ∀ u v, B u v = B v u) : B.IsSymm :=
  LinearMap.isSymm_def.2 fun u v => by simpa using h u v

/-- If both the real and the imaginary parts of the symmetrized form vanish on a pair, then
the symmetrized form itself vanishes. -/
lemma symCLM_eq_zero_of (H : V →L[ℝ] V →L[ℝ] ℂ) {u v : V}
    (hre : reForm H u v = 0) (him : imForm H u v = 0) : H u v + H v u = 0 := by
  rw [reForm_apply] at hre
  rw [imForm_apply] at him
  exact Complex.ext hre him


/-- **Step 1 of the simultaneous diagonalization.**  Coercivity makes the imaginary part of
the symmetrized form positive definite, so `V` has a basis orthonormal for it. -/
theorem exists_imForm_orthonormalBasis [FiniteDimensional ℝ V] (H : V →L[ℝ] V →L[ℝ] ℂ)
    {c : ℝ} (hc : 0 < c) (hH : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).im) :
    ∃ f : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i j, imForm H (f i) (f j) = if i = j then 1 else 0 := by
  have hpos : ∀ u : V, u ≠ 0 → 0 < imForm H u u := by
    intro u hu
    rw [imForm_self]
    have h1 := hH u
    have h2 : (0 : ℝ) < c * ‖u‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hu) 2)
    linarith
  obtain ⟨f, hf⟩ := LinearMap.BilinForm.exists_orthogonal_basis
      (B := imForm H) (isSymm_of_comm (imForm_comm H))
  have hfpos : ∀ i, 0 < imForm H (f i) (f i) := fun i => hpos (f i) (f.ne_zero i)
  have hne : ∀ i, (Real.sqrt (imForm H (f i) (f i)))⁻¹ ≠ 0 := fun i =>
    inv_ne_zero (Real.sqrt_pos.2 (hfpos i)).ne'
  refine ⟨f.unitsSMul (fun i => Units.mk0 _ (hne i)), ?_⟩
  intro i j
  rw [Module.Basis.unitsSMul_apply, Module.Basis.unitsSMul_apply]
  simp only [Units.smul_def, Units.val_mk0, map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hX : Real.sqrt (imForm H (f i) (f i)) * Real.sqrt (imForm H (f i) (f i))
        = imForm H (f i) (f i) := Real.mul_self_sqrt (hfpos i).le
    have hs : Real.sqrt (imForm H (f i) (f i)) ≠ 0 := (Real.sqrt_pos.2 (hfpos i)).ne'
    field_simp
    linarith [hX]
  · rw [if_neg hij, LinearMap.isOrthoᵢ_def.1 hf i j hij]
    ring


/-- **Simultaneous diagonalization.**  If the imaginary part of the complex quadratic form
`u ↦ H u u` is coercive, then `V` has a basis which is orthogonal for the symmetrized form of
`H`; equivalently, `H` is diagonal in the corresponding coordinates.

This is the classical simultaneous diagonalization of a pair of real symmetric bilinear forms
one of which is positive definite: an orthonormal basis for `Im H` (Gram–Schmidt) followed by
the spectral theorem for `Re H` in that basis. -/
theorem exists_orthoBasis_of_coercive [FiniteDimensional ℝ V] (H : V →L[ℝ] V →L[ℝ] ℂ)
    {c : ℝ} (hc : 0 < c) (hH : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).im) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i j, i ≠ j → H (b i) (b j) + H (b j) (b i) = 0 := by
  obtain ⟨f, hf⟩ := exists_imForm_orthonormalBasis H hc hH
  have hforth : ∀ i j, i ≠ j → imForm H (f i) (f j) = 0 := by
    intro i j hij
    rw [hf i j, if_neg hij]
  -- the linear equivalence `EuclideanSpace ℝ (Fin n) ≃ V` carrying the standard basis to `f`
  set Ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃ₗ[ℝ] V :=
    (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ V) → ℝ)).trans f.equivFun.symm with hΨ
  have hΨ_apply : ∀ x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      Ψ x = ∑ i, (WithLp.ofLp x i) • f i := by
    intro x
    rw [hΨ]
    simp [Module.Basis.equivFun_symm_apply]
  -- `Ψ` carries the Euclidean inner product to the imaginary part of the symmetrized form
  have hiso : ∀ x y : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      imForm H (Ψ x) (Ψ y) = ⟪x, y⟫ := by
    intro x y
    rw [hΨ_apply, hΨ_apply, bilin_orthogonal_sum _ _ hforth, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf i i, if_pos rfl, mul_one]
    simp [real_inner_eq_re_inner, mul_comm]
  -- the real part, transported to Euclidean space
  set A' : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    (reForm H).compl₁₂ Ψ.toLinearMap Ψ.toLinearMap with hA'
  have hA'_apply : ∀ x y, A' x y = reForm H (Ψ x) (Ψ y) := fun x y => rfl
  have hA'_symm : ∀ x y, A' x y = A' y x := fun x y => by
    rw [hA'_apply, hA'_apply, reForm_comm]
  -- the self-adjoint operator representing `A'`
  set P : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    { toFun := fun x =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).symm
          (LinearMap.toContinuousLinearMap (A' x))
      map_add' := by intro x y; simp
      map_smul' := by intro a x; simp } with hP
  have hPinner : ∀ x y, ⟪P x, y⟫ = A' x y := by
    intro x y
    exact InnerProductSpace.toDual_symm_apply
  have hPsymm : P.IsSymmetric := by
    intro x y
    rw [hPinner, real_inner_comm, hPinner, hA'_symm]
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
      = Module.finrank ℝ V := finrank_euclideanSpace_fin
  set wb := hPsymm.eigenvectorBasis hrank with hwb
  refine ⟨(wb.toBasis).map Ψ, ?_⟩
  intro i j hij
  have hbi : ((wb.toBasis).map Ψ) i = Ψ (wb i) := by simp
  have hbj : ((wb.toBasis).map Ψ) j = Ψ (wb j) := by simp
  rw [hbi, hbj]
  refine symCLM_eq_zero_of H ?_ ?_
  · have h1 : reForm H (Ψ (wb i)) (Ψ (wb j)) = A' (wb i) (wb j) := (hA'_apply _ _).symm
    rw [h1, ← hPinner, hPsymm.apply_eigenvectorBasis hrank i, real_inner_smul_left,
      wb.orthonormal.2 hij, mul_zero]
  · rw [hiso, wb.orthonormal.2 hij]


end Diagonalize

/-! ## 10.  Non-vanishing of the leading constant, in general -/

section Final

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Non-vanishing of the leading complex-Gaussian constant, in full generality.**

If the imaginary part of the complex Hessian `H` is coercive — which is exactly the
nondegeneracy hypothesis of Liu–Wang's Lemma 4.1 (iii) — then the leading constant
`∫ exp (i H(u,u)/2) dμ` of the stationary-phase expansion is non-zero, for *any* additive
Haar measure `μ` on any finite-dimensional real normed space `V`.

This is the constant `c ≠ 0` of equation (4.4). -/
theorem gaussConst_ne_zero (μ : Measure V) [μ.IsAddHaarMeasure]
    {H : V →L[ℝ] V →L[ℝ] ℂ} {c : ℝ} (hc : 0 < c)
    (hH : ∀ u : V, c * ‖u‖ ^ 2 ≤ (H u u).im) :
    gaussConst μ H ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_orthoBasis_of_coercive H hc hH
  exact gaussConst_ne_zero_of_orthoBasis μ hc hH b hb

end Final

end LiuWang2025SemilinearWaveComplexStationaryPhase
