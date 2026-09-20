/-
# Flat-space Gaussian beam amplitude: the paraxial core

This file constructs the transverse Gaussian amplitude

  `Aρ(s, x₁, x₂) = c(s)⁻¹ exp(-ρ r² / (2 c(s)))`,   `c(s) = 1 - i s / 2`,  `r² = x₁² + x₂²`,

computes **all** of its first and second partial derivatives from the actual Mathlib
derivative API (`HasDerivAt`), and proves:

* `cs_ne_zero`         : `c(s) ≠ 0` for every real `s`;
* `paraxial`           : `4 i ρ ∂_s Aρ - Δ_⊥ Aρ = 0`;
* `norm_A`             : the exact modulus `|Aρ| = (1+s²/4)^{-1/2} exp(-ρ r²/(2(1+s²/4)))`;
* `norm_A_le` / `le_norm_A` : quantitative Gaussian transverse localization on `|s| ≤ S`;
* `integral_normSq_A`  : the exact transverse `L²` mass `π/ρ`;
* `integral_normSq_Anorm` : the unit-mass normalization.

This is the calibration model for the reflected-beam step of the Liu–Wang partial-data
semilinear wave inverse problem.  Nothing here is postulated: every displayed derivative
is produced by `HasDerivAt` and then converted with `HasDerivAt.deriv`.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace LiuWang2025SemilinearWaveFlatBeam

noncomputable section

open MeasureTheory

/-! ## Transverse radius -/

/-- Squared transverse radius `r² = x₁² + x₂²`. -/
def rsq (x₁ x₂ : ℝ) : ℝ := x₁ ^ 2 + x₂ ^ 2

theorem rsq_nonneg (x₁ x₂ : ℝ) : 0 ≤ rsq x₁ x₂ := by
  unfold rsq; positivity

/-! ## The complex width parameter `c(s) = 1 - i s / 2` -/

/-- The complex beam width parameter `c(s) = 1 - i s / 2`. -/
def cs (s : ℝ) : ℂ := 1 - Complex.I * (s : ℂ) / 2

theorem cs_eq (s : ℝ) : cs s = (1 : ℂ) - ((s / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [cs]
  push_cast
  ring

@[simp] theorem cs_re (s : ℝ) : (cs s).re = 1 := by
  rw [cs_eq]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem cs_im (s : ℝ) : (cs s).im = -(s / 2) := by
  rw [cs_eq]
  simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **`c(s)` never vanishes**: its real part is identically `1`. -/
theorem cs_ne_zero (s : ℝ) : cs s ≠ 0 := by
  intro h
  have h1 : (cs s).re = 0 := by rw [h]; simp
  rw [cs_re] at h1
  exact one_ne_zero h1

theorem cs_pow_ne_zero (s : ℝ) (n : ℕ) : cs s ^ n ≠ 0 := pow_ne_zero _ (cs_ne_zero s)

theorem normSq_cs (s : ℝ) : Complex.normSq (cs s) = 1 + s ^ 2 / 4 := by
  rw [Complex.normSq_apply, cs_re, cs_im]; ring

theorem one_le_normSq_cs (s : ℝ) : 1 ≤ Complex.normSq (cs s) := by
  rw [normSq_cs]; nlinarith [sq_nonneg s]

/-- The exact modulus of the width parameter. -/
theorem norm_cs (s : ℝ) : ‖cs s‖ = Real.sqrt (1 + s ^ 2 / 4) := by
  rw [Complex.norm_def, normSq_cs]

theorem hasDerivAt_cs (s : ℝ) : HasDerivAt cs (-(Complex.I / 2)) s := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℝ) s := (hasDerivAt_id s).ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => (1 : ℂ) - Complex.I * (y : ℂ) / 2)
      (-(Complex.I * ((1 : ℝ) : ℂ) / 2)) s :=
    (((h.const_mul Complex.I).div_const 2).const_sub 1)
  exact h2.congr_deriv (by push_cast; ring)

theorem differentiable_cs : Differentiable ℝ cs := fun s => (hasDerivAt_cs s).differentiableAt

/-! ## The Gaussian exponent `-ρ r² / (2 c(s))` -/

/-- The Gaussian exponent `-ρ r² / (2 c(s))`. -/
def gaussArg (ρ s x₁ x₂ : ℝ) : ℂ := -((ρ * rsq x₁ x₂ : ℝ) : ℂ) / (2 * cs s)

/-- `∂_s` of the Gaussian exponent. -/
def dsGaussArg (ρ s x₁ x₂ : ℝ) : ℂ :=
  -(((ρ * rsq x₁ x₂ : ℝ) : ℂ) * Complex.I) / (4 * cs s ^ 2)

/-- `∂_{x₁}` of the Gaussian exponent. -/
def dx1GaussArg (ρ s x₁ _x₂ : ℝ) : ℂ := -((ρ * x₁ : ℝ) : ℂ) / cs s

/-- `∂_{x₂}` of the Gaussian exponent. -/
def dx2GaussArg (ρ s _x₁ x₂ : ℝ) : ℂ := -((ρ * x₂ : ℝ) : ℂ) / cs s

theorem two_cs_ne_zero (s : ℝ) : (2 : ℂ) * cs s ≠ 0 :=
  mul_ne_zero two_ne_zero (cs_ne_zero s)

theorem hasDerivAt_gaussArg_s (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun σ : ℝ => gaussArg ρ σ x₁ x₂) (dsGaussArg ρ s x₁ x₂) s := by
  have hden : HasDerivAt (fun σ : ℝ => 2 * cs σ) (2 * -(Complex.I / 2)) s :=
    (hasDerivAt_cs s).const_mul 2
  have h := (hasDerivAt_const s (-((ρ * rsq x₁ x₂ : ℝ) : ℂ))).fun_div hden (two_cs_ne_zero s)
  refine h.congr_deriv ?_
  simp only [dsGaussArg]
  have hc := cs_ne_zero s
  field_simp
  ring

theorem hasDerivAt_gaussArg_x1 (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun X : ℝ => gaussArg ρ s X x₂) (dx1GaussArg ρ s x₁ x₂) x₁ := by
  have h0 : HasDerivAt (fun X : ℝ => X ^ 2) (2 * x₁) x₁ := by
    simpa using hasDerivAt_pow 2 x₁
  have hr : HasDerivAt (fun X : ℝ => ρ * rsq X x₂) (ρ * (2 * x₁)) x₁ := by
    simpa only [rsq] using (h0.add_const (x₂ ^ 2)).const_mul ρ
  have h := (hr.ofReal_comp.neg.div_const (2 * cs s))
  refine h.congr_deriv ?_
  simp only [dx1GaussArg]
  have hc := cs_ne_zero s
  push_cast
  field_simp

theorem hasDerivAt_gaussArg_x2 (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun X : ℝ => gaussArg ρ s x₁ X) (dx2GaussArg ρ s x₁ x₂) x₂ := by
  have h0 : HasDerivAt (fun X : ℝ => X ^ 2) (2 * x₂) x₂ := by
    simpa using hasDerivAt_pow 2 x₂
  have hr : HasDerivAt (fun X : ℝ => ρ * rsq x₁ X) (ρ * (2 * x₂)) x₂ := by
    simpa only [rsq] using (h0.const_add (x₁ ^ 2)).const_mul ρ
  have h := (hr.ofReal_comp.neg.div_const (2 * cs s))
  refine h.congr_deriv ?_
  simp only [dx2GaussArg]
  have hc := cs_ne_zero s
  push_cast
  field_simp

/-- The real part of the Gaussian exponent: this is what controls the modulus. -/
theorem gaussArg_re (ρ s x₁ x₂ : ℝ) :
    (gaussArg ρ s x₁ x₂).re = -(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)) := by
  have hpos : (0 : ℝ) < 1 + s ^ 2 / 4 := by positivity
  have hane : (1 + s ^ 2 / 4 : ℝ) ≠ 0 := ne_of_gt hpos
  have hre : ((2 : ℂ) * cs s).re = 2 := by
    simp [Complex.mul_re]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  have hnsq : Complex.normSq ((2 : ℂ) * cs s) = 4 * (1 + s ^ 2 / 4) := by
    rw [map_mul, normSq_cs, h2]
  have hgeq : gaussArg ρ s x₁ x₂ = ((-(ρ * rsq x₁ x₂) : ℝ) : ℂ) * ((2 : ℂ) * cs s)⁻¹ := by
    rw [gaussArg, div_eq_mul_inv]; push_cast; ring
  rw [hgeq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.inv_re, hre, hnsq]
  field_simp
  ring

/-! ## The Gaussian amplitude `Aρ` and its derivatives -/

/-- The transverse Gaussian amplitude `Aρ(s,x₁,x₂) = c(s)⁻¹ exp(-ρ r²/(2c(s)))`. -/
def A (ρ s x₁ x₂ : ℝ) : ℂ := (cs s)⁻¹ * Complex.exp (gaussArg ρ s x₁ x₂)

theorem A_eq_div (ρ s x₁ x₂ : ℝ) :
    A ρ s x₁ x₂ = Complex.exp (gaussArg ρ s x₁ x₂) / cs s := by
  rw [A, div_eq_inv_mul]

/-- `∂_s Aρ`, in closed form. -/
def dsA (ρ s x₁ x₂ : ℝ) : ℂ :=
  Complex.exp (gaussArg ρ s x₁ x₂) *
    (2 * Complex.I * cs s - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)) / (4 * cs s ^ 3)

/-- `∂_{x₁} Aρ`, in closed form. -/
def dx1A (ρ s x₁ x₂ : ℝ) : ℂ :=
  -((ρ * x₁ : ℝ) : ℂ) * Complex.exp (gaussArg ρ s x₁ x₂) / cs s ^ 2

/-- `∂_{x₂} Aρ`, in closed form. -/
def dx2A (ρ s x₁ x₂ : ℝ) : ℂ :=
  -((ρ * x₂ : ℝ) : ℂ) * Complex.exp (gaussArg ρ s x₁ x₂) / cs s ^ 2

/-- `∂²_{x₁} Aρ`, in closed form. -/
def dx1x1A (ρ s x₁ x₂ : ℝ) : ℂ :=
  Complex.exp (gaussArg ρ s x₁ x₂) * (-(ρ : ℂ) * cs s + (ρ : ℂ) ^ 2 * (x₁ : ℂ) ^ 2) / cs s ^ 3

/-- `∂²_{x₂} Aρ`, in closed form. -/
def dx2x2A (ρ s x₁ x₂ : ℝ) : ℂ :=
  Complex.exp (gaussArg ρ s x₁ x₂) * (-(ρ : ℂ) * cs s + (ρ : ℂ) ^ 2 * (x₂ : ℂ) ^ 2) / cs s ^ 3

/-- The transverse Laplacian `Δ_⊥ Aρ = ∂²_{x₁} Aρ + ∂²_{x₂} Aρ`. -/
def lapA (ρ s x₁ x₂ : ℝ) : ℂ := dx1x1A ρ s x₁ x₂ + dx2x2A ρ s x₁ x₂

theorem hasDerivAt_A_s (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun σ : ℝ => A ρ σ x₁ x₂) (dsA ρ s x₁ x₂) s := by
  have hfun : (fun σ : ℝ => A ρ σ x₁ x₂)
      = fun σ : ℝ => Complex.exp (gaussArg ρ σ x₁ x₂) / cs σ := by
    funext σ; exact A_eq_div ρ σ x₁ x₂
  rw [hfun]
  refine (((hasDerivAt_gaussArg_s ρ s x₁ x₂).cexp).fun_div (hasDerivAt_cs s)
    (cs_ne_zero s)).congr_deriv ?_
  simp only [dsA, dsGaussArg]
  have hc := cs_ne_zero s
  field_simp
  ring

theorem hasDerivAt_A_x1 (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun X : ℝ => A ρ s X x₂) (dx1A ρ s x₁ x₂) x₁ := by
  refine (((hasDerivAt_gaussArg_x1 ρ s x₁ x₂).cexp).const_mul (cs s)⁻¹).congr_deriv ?_
  simp only [dx1A, dx1GaussArg]
  have hc := cs_ne_zero s
  field_simp

theorem hasDerivAt_A_x2 (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun X : ℝ => A ρ s x₁ X) (dx2A ρ s x₁ x₂) x₂ := by
  refine (((hasDerivAt_gaussArg_x2 ρ s x₁ x₂).cexp).const_mul (cs s)⁻¹).congr_deriv ?_
  simp only [dx2A, dx2GaussArg]
  have hc := cs_ne_zero s
  field_simp

theorem hasDerivAt_dx1A (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun X : ℝ => dx1A ρ s X x₂) (dx1x1A ρ s x₁ x₂) x₁ := by
  have hlin : HasDerivAt (fun X : ℝ => -(ρ * X)) (-ρ) x₁ := by
    simpa using ((hasDerivAt_id x₁).const_mul ρ).neg
  have hnum := hlin.ofReal_comp.fun_mul ((hasDerivAt_gaussArg_x1 ρ s x₁ x₂).cexp)
  have h := hnum.div_const (cs s ^ 2)
  have hfun : (fun X : ℝ => dx1A ρ s X x₂)
      = fun X : ℝ => ((-(ρ * X) : ℝ) : ℂ) * Complex.exp (gaussArg ρ s X x₂) / cs s ^ 2 := by
    funext X; simp only [dx1A]; push_cast; ring
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [dx1x1A, dx1GaussArg]
  have hc := cs_ne_zero s
  push_cast
  field_simp

theorem hasDerivAt_dx2A (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun X : ℝ => dx2A ρ s x₁ X) (dx2x2A ρ s x₁ x₂) x₂ := by
  have hlin : HasDerivAt (fun X : ℝ => -(ρ * X)) (-ρ) x₂ := by
    simpa using ((hasDerivAt_id x₂).const_mul ρ).neg
  have hnum := hlin.ofReal_comp.fun_mul ((hasDerivAt_gaussArg_x2 ρ s x₁ x₂).cexp)
  have h := hnum.div_const (cs s ^ 2)
  have hfun : (fun X : ℝ => dx2A ρ s x₁ X)
      = fun X : ℝ => ((-(ρ * X) : ℝ) : ℂ) * Complex.exp (gaussArg ρ s x₁ X) / cs s ^ 2 := by
    funext X; simp only [dx2A]; push_cast; ring
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [dx2x2A, dx2GaussArg]
  have hc := cs_ne_zero s
  push_cast
  field_simp

/-! ### The second `s`-derivative

`∂²_s Aρ` is not needed in closed form: it cancels identically from `□`.  We only need that
it *exists*, which we obtain from an honest `HasDerivAt` chain for `dsA`. -/

theorem differentiableAt_dsA (ρ s x₁ x₂ : ℝ) :
    DifferentiableAt ℝ (fun σ : ℝ => dsA ρ σ x₁ x₂) s := by
  have hnum := ((hasDerivAt_gaussArg_s ρ s x₁ x₂).cexp).fun_mul
    (((hasDerivAt_cs s).const_mul (2 * Complex.I)).sub_const
      (Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)))
  have hden := ((hasDerivAt_cs s).pow 3).const_mul (4 : ℂ)
  have hne : (4 : ℂ) * cs s ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (cs_pow_ne_zero s 3)
  exact (hnum.fun_div hden hne).differentiableAt

/-- `∂²_s Aρ`, defined as the derivative of the explicit first derivative. -/
def d2sA (ρ s x₁ x₂ : ℝ) : ℂ := deriv (fun σ : ℝ => dsA ρ σ x₁ x₂) s

theorem hasDerivAt_dsA (ρ s x₁ x₂ : ℝ) :
    HasDerivAt (fun σ : ℝ => dsA ρ σ x₁ x₂) (d2sA ρ s x₁ x₂) s :=
  (differentiableAt_dsA ρ s x₁ x₂).hasDerivAt

/-! ## The paraxial (Schrödinger) equation -/

private theorem paraxial_alg (E c P X Y : ℂ) (hc : c ≠ 0) :
    4 * Complex.I * P * (E * (2 * Complex.I * c - Complex.I * (P * (X ^ 2 + Y ^ 2))) /
        (4 * c ^ 3))
      = E * (-P * c + P ^ 2 * X ^ 2) / c ^ 3 + E * (-P * c + P ^ 2 * Y ^ 2) / c ^ 3 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have key : 4 * Complex.I * P *
      (E * (2 * Complex.I * c - Complex.I * (P * (X ^ 2 + Y ^ 2))) / (4 * c ^ 3))
      = Complex.I * Complex.I * (E * (2 * P * c - P ^ 2 * (X ^ 2 + Y ^ 2)) / c ^ 3) := by
    field_simp
  rw [key, hI]
  field_simp
  ring

/-- **The paraxial equation.**  `4 i ρ ∂_s Aρ - Δ_⊥ Aρ = 0`, with both derivatives computed
from `HasDerivAt`. -/
theorem paraxial (ρ s x₁ x₂ : ℝ) :
    4 * Complex.I * (ρ : ℂ) * dsA ρ s x₁ x₂ - lapA ρ s x₁ x₂ = 0 := by
  rw [sub_eq_zero]
  simp only [dsA, lapA, dx1x1A, dx2x2A, rsq]
  push_cast
  exact paraxial_alg _ _ _ _ _ (cs_ne_zero s)

/-- The paraxial equation phrased directly with `deriv`. -/
theorem paraxial_deriv (ρ s x₁ x₂ : ℝ) :
    4 * Complex.I * (ρ : ℂ) * deriv (fun σ : ℝ => A ρ σ x₁ x₂) s
      - (deriv (fun X : ℝ => deriv (fun Y : ℝ => A ρ s Y x₂) X) x₁
         + deriv (fun X : ℝ => deriv (fun Y : ℝ => A ρ s x₁ Y) X) x₂) = 0 := by
  have h1 : deriv (fun σ : ℝ => A ρ σ x₁ x₂) s = dsA ρ s x₁ x₂ :=
    (hasDerivAt_A_s ρ s x₁ x₂).deriv
  have h2 : deriv (fun X : ℝ => deriv (fun Y : ℝ => A ρ s Y x₂) X) x₁ = dx1x1A ρ s x₁ x₂ := by
    have e : (fun X : ℝ => deriv (fun Y : ℝ => A ρ s Y x₂) X) = fun X : ℝ => dx1A ρ s X x₂ := by
      funext X; exact (hasDerivAt_A_x1 ρ s X x₂).deriv
    rw [e]; exact (hasDerivAt_dx1A ρ s x₁ x₂).deriv
  have h3 : deriv (fun X : ℝ => deriv (fun Y : ℝ => A ρ s x₁ Y) X) x₂ = dx2x2A ρ s x₁ x₂ := by
    have e : (fun X : ℝ => deriv (fun Y : ℝ => A ρ s x₁ Y) X) = fun X : ℝ => dx2A ρ s x₁ X := by
      funext X; exact (hasDerivAt_A_x2 ρ s x₁ X).deriv
    rw [e]; exact (hasDerivAt_dx2A ρ s x₁ x₂).deriv
  rw [h1, h2, h3]
  simpa only [lapA] using paraxial ρ s x₁ x₂

/-! ## Exact modulus and quantitative Gaussian localization -/

/-- **Exact modulus formula.** -/
theorem norm_A (ρ s x₁ x₂ : ℝ) :
    ‖A ρ s x₁ x₂‖
      = (Real.sqrt (1 + s ^ 2 / 4))⁻¹ *
          Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4))) := by
  rw [A, norm_mul, norm_inv, norm_cs, Complex.norm_exp, gaussArg_re]

theorem one_le_sqrt_cs (s : ℝ) : 1 ≤ Real.sqrt (1 + s ^ 2 / 4) := by
  have h : (1 : ℝ) ≤ 1 + s ^ 2 / 4 := by nlinarith [sq_nonneg s]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + s ^ 2 / 4) := Real.sqrt_le_sqrt h

theorem sqrt_cs_pos (s : ℝ) : 0 < Real.sqrt (1 + s ^ 2 / 4) :=
  lt_of_lt_of_le one_pos (one_le_sqrt_cs s)

/-- **Quantitative Gaussian transverse localization**, uniformly on the bounded `s`-interval
`|s| ≤ S`: the amplitude is dominated by a fixed Gaussian of width set by `S`. -/
theorem norm_A_le (ρ : ℝ) (hρ : 0 ≤ ρ) (S s : ℝ) (hs : |s| ≤ S) (x₁ x₂ : ℝ) :
    ‖A ρ s x₁ x₂‖ ≤ Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + S ^ 2 / 4))) := by
  have hsq : s ^ 2 ≤ S ^ 2 := by
    have h := abs_nonneg s
    nlinarith [sq_abs s, abs_nonneg s]
  have hpos : (0 : ℝ) < 1 + s ^ 2 / 4 := by positivity
  have hPos : (0 : ℝ) < 1 + S ^ 2 / 4 := by nlinarith [sq_nonneg s]
  have hK : 0 ≤ ρ * rsq x₁ x₂ := mul_nonneg hρ (rsq_nonneg x₁ x₂)
  have hmono : -(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4))
      ≤ -(ρ * rsq x₁ x₂) / (2 * (1 + S ^ 2 / 4)) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  rw [norm_A]
  have h1 : (Real.sqrt (1 + s ^ 2 / 4))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_sqrt_cs s)
  calc (Real.sqrt (1 + s ^ 2 / 4))⁻¹ * Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)))
      ≤ 1 * Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4))) := by
        gcongr
    _ = Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4))) := one_mul _
    _ ≤ Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + S ^ 2 / 4))) := Real.exp_le_exp.2 hmono

/-- Matching lower bound on `|s| ≤ S`: the beam is genuinely of Gaussian size, not smaller. -/
theorem le_norm_A (ρ : ℝ) (hρ : 0 ≤ ρ) (S s : ℝ) (hs : |s| ≤ S) (x₁ x₂ : ℝ) :
    (Real.sqrt (1 + S ^ 2 / 4))⁻¹ * Real.exp (-(ρ * rsq x₁ x₂) / 2) ≤ ‖A ρ s x₁ x₂‖ := by
  have hsq : s ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  have hpos : (0 : ℝ) < 1 + s ^ 2 / 4 := by positivity
  have hane : (1 + s ^ 2 / 4 : ℝ) ≠ 0 := ne_of_gt hpos
  have hK : 0 ≤ ρ * rsq x₁ x₂ := mul_nonneg hρ (rsq_nonneg x₁ x₂)
  have hmono : -(ρ * rsq x₁ x₂) / 2 ≤ -(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)) := by
    rw [← sub_nonneg]
    have key : -(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)) - -(ρ * rsq x₁ x₂) / 2
        = ρ * rsq x₁ x₂ * s ^ 2 / (8 * (1 + s ^ 2 / 4)) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (mul_nonneg hK (sq_nonneg s)) (by positivity)
  have hsle : Real.sqrt (1 + s ^ 2 / 4) ≤ Real.sqrt (1 + S ^ 2 / 4) :=
    Real.sqrt_le_sqrt (by linarith)
  have hinv : (Real.sqrt (1 + S ^ 2 / 4))⁻¹ ≤ (Real.sqrt (1 + s ^ 2 / 4))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hpos) hsle
  rw [norm_A]
  exact mul_le_mul hinv (Real.exp_le_exp.2 hmono) (Real.exp_pos _).le
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-! ## Exact transverse `L²` mass and unit-mass normalization -/

/-- **Exact transverse `L²` mass.**  For every `s`, the transverse mass of `Aρ(s,·,·)` equals
`π/ρ`; in particular it is independent of `s`. -/
theorem integral_normSq_A (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    (∫ p : ℝ × ℝ, ‖A ρ s p.1 p.2‖ ^ 2) = Real.pi / ρ := by
  have ha0 : (0 : ℝ) < 1 + s ^ 2 / 4 := by positivity
  have ha' : (1 + s ^ 2 / 4) ≠ 0 := ne_of_gt ha0
  have hρ' : ρ ≠ 0 := ne_of_gt hρ
  have hb0 : (0 : ℝ) < ρ / (1 + s ^ 2 / 4) := div_pos hρ ha0
  have key : ∀ p : ℝ × ℝ, ‖A ρ s p.1 p.2‖ ^ 2
      = (1 + s ^ 2 / 4)⁻¹ *
          (Real.exp (-(ρ / (1 + s ^ 2 / 4)) * p.1 ^ 2) *
            Real.exp (-(ρ / (1 + s ^ 2 / 4)) * p.2 ^ 2)) := by
    intro p
    rw [norm_A, mul_pow]
    congr 1
    · rw [inv_pow, Real.sq_sqrt ha0.le]
    · rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [rsq]
      field_simp
      ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul
      (fun x : ℝ => Real.exp (-(ρ / (1 + s ^ 2 / 4)) * x ^ 2))
      (fun x : ℝ => Real.exp (-(ρ / (1 + s ^ 2 / 4)) * x ^ 2)),
    integral_gaussian, Real.mul_self_sqrt (le_of_lt (div_pos Real.pi_pos hb0))]
  field_simp

/-- The unit-transverse-mass normalization of the Gaussian amplitude. -/
def Anorm (ρ s x₁ x₂ : ℝ) : ℂ := ((Real.sqrt (ρ / Real.pi) : ℝ) : ℂ) * A ρ s x₁ x₂

theorem norm_Anorm_sq (ρ : ℝ) (hρ : 0 < ρ) (s x₁ x₂ : ℝ) :
    ‖Anorm ρ s x₁ x₂‖ ^ 2 = (ρ / Real.pi) * ‖A ρ s x₁ x₂‖ ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Anorm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (div_nonneg hρ.le Real.pi_pos.le)]

/-- **Unit transverse mass after normalization.** -/
theorem integral_normSq_Anorm (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    (∫ p : ℝ × ℝ, ‖Anorm ρ s p.1 p.2‖ ^ 2) = 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  simp_rw [norm_Anorm_sq ρ hρ]
  rw [MeasureTheory.integral_const_mul, integral_normSq_A ρ hρ s]
  field_simp

end

end LiuWang2025SemilinearWaveFlatBeam
